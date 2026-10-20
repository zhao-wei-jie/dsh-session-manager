import { dshHomePath } from "@deepseek-ai/dsh-home-paths";
import { defineDomain } from "@deepseek-ai/dsh-storage-domain";
import { z } from "zod";
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, rm, stat, writeFile } from "node:fs/promises";
import { execFile, spawn } from "node:child_process";
import { dirname, isAbsolute, join, relative, resolve } from "node:path";
import { createHash } from "node:crypto";
import { promisify } from "node:util";
//#region src/workspace.ts
/**
* Hidden-git workspace snapshots backing "undo last turn".
*
* Ported from dsh-undo (MIT, https://github.com/LingLambda/dsh-undo) and adapted
* to the DSH 0.2.x API surface: there is no `surface/rewind`, no `session.events`
* array and no `activeRewinds` journal here, so
*
*  - every session keeps its own bare git repository under
*    `<dshHome>/dsh-session-manager/snapshots/<hash>/`;
*  - each root tool call records the tree before and after it (`{ callSeq, before, files }`);
*  - an undo restores each affected file to its earliest pre-call tree and keeps
*    the pre-undo tree as a redo entry;
*  - crash recovery uses this file's own `pending` journal instead of a surface
*    rewind stack.
*
* The session log stays authoritative for the conversation; this module only
* mirrors the workspace files a turn touched.
*
* @module dsh-session-manager/workspace
*/
const execFileAsync = promisify(execFile);
/** Untracked files larger than this stay out of snapshots. */
const MAX_UNTRACKED_BYTES = 2 * 1024 * 1024;
/** Turns retained per session; older patches are dropped. */
const MAX_RETAINED_TURNS = 50;
const STATE_VERSION = 1;
/** A missing or unusable git workspace, as a user-facing warning. */
const GIT_MISSING_TEXT = "工作区快照不可用(未找到 git 仓库或 git 命令),本次只回退了对话。";
/**
* One session's hidden-git workspace checkpoints.
*
* All git work is serialized: the runtime dispatches parallel tool calls, and a
* hidden repository cannot take two `write-tree` writers at once.
*/
var WorkspaceSnapshots = class {
	options;
	root;
	gitDir;
	unavailable;
	initPromise;
	loaded = false;
	state = {
		version: STATE_VERSION,
		patches: {},
		redos: {}
	};
	gitTail = Promise.resolve();
	stateTail = Promise.resolve();
	constructor(options) {
		this.options = options;
	}
	/**
	* Snapshot the workspace around one root tool call.
	*
	* Never throws on snapshot work: a failing mirror must not fail the tool.
	*
	* @param exec - the dispatch about to run.
	* @param next - the rest of the waterfall.
	* @param events - the session's committed events, read before and after.
	* @returns the tool result, unchanged.
	*/
	async around(exec, next, events) {
		if (exec.parent !== void 0) return next();
		const callId = String(exec.rootCallId);
		let userSeq;
		let before;
		try {
			userSeq = userSeqForCall(events(), callId);
			if (userSeq !== void 0) before = await this.snapshot();
		} catch (error) {
			this.options.logger.warn("[dsh-session-manager] workspace snapshot before the tool call failed:", error);
		}
		let result;
		try {
			result = await next();
		} finally {
			if (userSeq !== void 0 && before !== void 0) try {
				await this.recordCallPatches(userSeq, callId, before, events());
			} catch (error) {
				this.options.logger.warn("[dsh-session-manager] workspace snapshot after the tool call failed:", error);
			}
		}
		return result;
	}
	/**
	* Restore every file touched by the given user turns.
	*
	* Writes a `pending` journal before touching the workspace, so an interrupted
	* restore is compensated by the next {@link restore}, {@link rollback} or
	* {@link redo} call.
	*
	* @param userSeqs - user message sequences to unwind (the target turn and any later ones).
	* @param opId - caller-chosen operation id used by {@link commit} / {@link rollback}.
	* @returns restored file count, or a warning when the mirror is unavailable.
	*/
	async restore(userSeqs, opId) {
		if (!await this.initialize()) return {
			files: 0,
			warning: this.unavailable ?? GIT_MISSING_TEXT
		};
		await this.recoverPending();
		const patches = [...new Set(userSeqs)].flatMap((seq) => this.state.patches[String(seq)] ?? []).sort((a, b) => a.callSeq - b.callSeq);
		if (patches.length === 0) return { files: 0 };
		const current = await this.snapshot();
		if (current === void 0) return {
			files: 0,
			warning: this.unavailable ?? GIT_MISSING_TEXT
		};
		const firstByFile = /* @__PURE__ */ new Map();
		for (const patch of patches) for (const file of patch.files) {
			if (firstByFile.has(file)) continue;
			if (await this.isExcludedCurrentFile(file)) continue;
			firstByFile.set(file, patch.before);
		}
		if (firstByFile.size === 0) return { files: 0 };
		const target = [...firstByFile].map(([file, tree]) => ({
			file,
			tree
		}));
		const rollback = {
			tree: current,
			files: [...firstByFile.keys()]
		};
		this.state.pending = {
			opId,
			rollback,
			target
		};
		await this.persistState();
		try {
			await this.restoreTargets(target);
		} catch (error) {
			await this.restoreRedo(rollback).catch((rollbackError) => {
				this.options.logger.warn("[dsh-session-manager] workspace compensation failed:", rollbackError);
			});
			this.state.pending = void 0;
			await this.persistState().catch(() => {});
			throw error;
		}
		return { files: target.length };
	}
	/**
	* Mark an undo as applied: its pre-undo tree becomes the redo entry.
	*
	* @param opId - operation id handed to {@link restore}.
	*/
	async commit(opId) {
		const pending = this.state.pending;
		if (pending === void 0 || pending.opId !== opId) return;
		this.state.redos[opId] = pending.rollback;
		this.state.pending = void 0;
		await this.persistState();
	}
	/**
	* Undo one {@link restore} that could not be completed: put the files back to
	* the pre-undo tree.
	*
	* @param opId - operation id handed to {@link restore}.
	*/
	async rollback(opId) {
		const pending = this.state.pending;
		if (pending === void 0 || pending.opId !== opId) return;
		await this.restoreRedo(pending.rollback);
		this.state.pending = void 0;
		await this.persistState();
	}
	/**
	* Re-apply the pre-undo tree recorded by an earlier {@link commit}.
	*
	* @param opId - operation id of the undo to reverse.
	* @returns restored file count.
	*/
	async redo(opId) {
		if (!await this.initialize()) return {
			files: 0,
			warning: this.unavailable ?? GIT_MISSING_TEXT
		};
		await this.recoverPending();
		const redo = this.state.redos[opId];
		if (redo === void 0) return { files: 0 };
		await this.restoreRedo(redo);
		delete this.state.redos[opId];
		await this.persistState();
		return { files: redo.files.length };
	}
	/**
	* Record one call's changed files, keyed by the turn it belongs to.
	*
	* @param userSeq - user message that started the turn.
	* @param callId - root tool call identity.
	* @param before - tree captured before the call.
	* @param events - committed events read after the call.
	*/
	async recordCallPatches(userSeq, callId, before, events) {
		const after = await this.snapshot();
		if (after === void 0 || after === before) return;
		const files = await this.changedFiles(before, after);
		if (files.length === 0) return;
		const callSeq = callSeqForCall(events, callId) ?? Number.MAX_SAFE_INTEGER;
		const key = String(userSeq);
		const list = this.state.patches[key] ?? [];
		list.push({
			callSeq,
			before,
			files
		});
		this.state.patches[key] = list;
		this.pruneTurns();
		await this.persistState();
	}
	/** Drop the oldest turns once the per-session budget is exceeded. */
	pruneTurns() {
		const keys = Object.keys(this.state.patches);
		if (keys.length <= MAX_RETAINED_TURNS) return;
		keys.map(Number).sort((a, b) => a - b).slice(0, keys.length - MAX_RETAINED_TURNS).forEach((seq) => delete this.state.patches[String(seq)]);
	}
	/** Compensate an operation interrupted between its journal write and commit. */
	async recoverPending() {
		const pending = this.state.pending;
		if (pending === void 0) return;
		try {
			await this.restoreRedo(pending.rollback);
			this.options.logger.warn("[dsh-session-manager] recovered an interrupted workspace undo; files were restored to the pre-undo state");
		} catch (error) {
			this.options.logger.warn("[dsh-session-manager] could not recover an interrupted workspace undo:", error);
		}
		this.state.pending = void 0;
		await this.persistState().catch(() => {});
	}
	/** Resolve the workspace root and open (or create) the hidden repository. */
	initialize() {
		if (this.initPromise !== void 0) return this.initPromise;
		this.initPromise = this.initializeOnce();
		return this.initPromise;
	}
	async initializeOnce() {
		const cwd = this.options.cwd;
		if (cwd === void 0 || cwd === "") {
			this.unavailable = "会话没有工作目录,本次只回退了对话。";
			return false;
		}
		try {
			const { stdout } = await execFileAsync("git", [
				"-C",
				cwd,
				"rev-parse",
				"--show-toplevel"
			], { encoding: "utf8" });
			const root = resolve(stdout.trim());
			if (isInside(this.options.storeRoot, root)) {
				this.unavailable = "工作区快照目录位于当前仓库内,已跳过文件回退,本次只回退了对话。";
				return false;
			}
			this.root = root;
			const key = createHash("sha256").update(root).update("\0").update(String(this.options.sessionId)).digest("hex").slice(0, 24);
			this.gitDir = join(this.options.storeRoot, key);
			await mkdir(this.gitDir, { recursive: true });
			try {
				await this.git(["rev-parse", "--is-bare-repository"]);
			} catch {
				await execFileAsync("git", [
					"init",
					"--bare",
					this.gitDir
				], { encoding: "utf8" });
				await this.git([
					"config",
					"core.autocrlf",
					"false"
				]);
				await this.git([
					"config",
					"core.longpaths",
					"true"
				]);
			}
			await this.loadState();
			return true;
		} catch (error) {
			this.unavailable = `工作区快照不可用(${error instanceof Error ? error.message : String(error)}),本次只回退了对话。`;
			return false;
		}
	}
	/** Mirror the current tracked + untracked workspace into one tree. */
	async snapshot() {
		if (!await this.initialize()) return void 0;
		return this.serialGit(async () => {
			const tracked = this.splitPaths(await this.sourceGit([
				"ls-files",
				"-z",
				"--cached",
				"--",
				"."
			]));
			const untracked = this.splitPaths(await this.sourceGit([
				"ls-files",
				"-z",
				"--others",
				"--exclude-standard",
				"--",
				"."
			]));
			const allowed = [];
			for (const file of untracked) try {
				const info = await stat(join(this.requireRoot(), file));
				if (!info.isFile() || info.size <= MAX_UNTRACKED_BYTES) allowed.push(file);
			} catch {}
			const candidates = [.../* @__PURE__ */ new Set([...tracked, ...allowed])];
			for (const batch of this.pathBatches(candidates)) await this.git([
				"add",
				"--all",
				"--",
				...batch.map((file) => `:(top,literal)${file}`)
			]);
			const candidateSet = new Set(candidates);
			const deleted = this.splitPaths(await this.git(["ls-files", "-z"])).filter((file) => !candidateSet.has(file));
			for (const batch of this.pathBatches(deleted)) await this.git([
				"rm",
				"--cached",
				"-f",
				"--ignore-unmatch",
				"--",
				...batch.map((file) => `:(top,literal)${file}`)
			]);
			return (await this.git(["write-tree"])).trim();
		});
	}
	/** Files whose content differs between two trees, minus ignored/oversized ones. */
	async changedFiles(before, after) {
		const output = await this.serialGit(() => this.git([
			"diff",
			"--name-only",
			"-z",
			before,
			after,
			"--",
			"."
		]));
		const filtered = [];
		for (const file of output.split("\0").filter(Boolean)) if (!await this.isExcludedCurrentFile(file)) filtered.push(file);
		return filtered;
	}
	/** Whether a path is ignored now and not tracked, or an oversized untracked file. */
	async isExcludedCurrentFile(file) {
		const root = this.requireRoot();
		try {
			await execFileAsync("git", [
				"-C",
				root,
				"check-ignore",
				"--no-index",
				"--quiet",
				"--",
				file
			], { encoding: "utf8" });
			return true;
		} catch (error) {
			if (error.code !== 1) throw error;
		}
		try {
			await execFileAsync("git", [
				"-C",
				root,
				"ls-files",
				"--error-unmatch",
				"--",
				file
			], { encoding: "utf8" });
			return false;
		} catch (error) {
			if (error.code !== 1) throw error;
		}
		try {
			const info = await stat(join(root, file));
			return info.isFile() && info.size > MAX_UNTRACKED_BYTES;
		} catch {
			return false;
		}
	}
	/** Restore one file (or delete it when the tree does not contain it). */
	async restoreFile(tree, file) {
		const literal = `:(top,literal)${file}`;
		if (!(await this.serialGit(() => this.git([
			"ls-tree",
			"-r",
			"--name-only",
			"-z",
			tree,
			"--",
			literal
		]))).split("\0").includes(file)) {
			await rm(join(this.requireRoot(), file), {
				recursive: true,
				force: true
			});
			return;
		}
		await this.serialGit(() => this.git([
			"checkout",
			tree,
			"--",
			literal
		]));
	}
	async restoreTargets(targets) {
		for (const target of targets) await this.restoreFile(target.tree, target.file);
	}
	async restoreRedo(redo) {
		for (const file of redo.files) await this.restoreFile(redo.tree, file);
	}
	async loadState() {
		if (this.gitDir === void 0 || this.loaded) return;
		this.loaded = true;
		try {
			const parsed = JSON.parse(await readFile(join(this.gitDir, "state.json"), "utf8"));
			if (parsed.version === STATE_VERSION) this.state = {
				version: STATE_VERSION,
				patches: parsed.patches ?? {},
				redos: parsed.redos ?? {},
				...parsed.pending === void 0 ? {} : { pending: parsed.pending }
			};
		} catch {}
	}
	persistState() {
		return this.serialState(async () => {
			if (this.gitDir === void 0) return;
			const path = join(this.gitDir, "state.json");
			const temporary = `${path}.tmp`;
			await writeFile(temporary, JSON.stringify(this.state), "utf8");
			await rename(temporary, path);
		});
	}
	serialGit(operation) {
		const result = this.gitTail.then(operation, operation);
		this.gitTail = result.then(() => void 0, () => void 0);
		return result;
	}
	serialState(operation) {
		const result = this.stateTail.then(operation, operation);
		this.stateTail = result.then(() => void 0, () => void 0);
		return result;
	}
	requireRoot() {
		if (this.root === void 0) throw new Error("workspace root is unavailable");
		return this.root;
	}
	async git(args) {
		const root = this.requireRoot();
		if (this.gitDir === void 0) throw new Error("snapshot git directory is unavailable");
		const { stdout } = await execFileAsync("git", [
			"-c",
			"core.autocrlf=false",
			"-c",
			"core.longpaths=true",
			"--git-dir",
			this.gitDir,
			"--work-tree",
			root,
			...args
		], {
			cwd: root,
			encoding: "utf8",
			maxBuffer: 16 * 1024 * 1024
		});
		return stdout;
	}
	async sourceGit(args) {
		const { stdout } = await execFileAsync("git", [
			"-C",
			this.requireRoot(),
			...args
		], {
			encoding: "utf8",
			maxBuffer: 16 * 1024 * 1024
		});
		return stdout;
	}
	splitPaths(output) {
		return output.split("\0").filter(Boolean);
	}
	pathBatches(paths) {
		const batches = [];
		let batch = [];
		let length = 0;
		for (const path of paths) {
			if (batch.length > 0 && length + path.length > 24e3) {
				batches.push(batch);
				batch = [];
				length = 0;
			}
			batch.push(path);
			length += path.length + 16;
		}
		if (batch.length > 0) batches.push(batch);
		return batches;
	}
};
/** The user message that owns one tool call: latest `user/message` before it. */
function userSeqForCall(events, callId) {
	const callSeq = callSeqForCall(events, callId);
	if (callSeq === void 0) return void 0;
	let found;
	for (const event of events) {
		if (event.seq >= callSeq) break;
		if (event.type !== "user/message") continue;
		if (event.data?.source?.kind !== "user") continue;
		found = event.seq;
	}
	return found;
}
/** Sequence of one tool call event. */
function callSeqForCall(events, callId) {
	for (const event of events) {
		if (event.type !== "tool/call") continue;
		const data = event.data;
		if (String(data?.callId) === callId) return event.seq;
	}
}
/** Whether `child` is `parent` or sits underneath it. */
function isInside(child, parent) {
	const rel = relative(parent, resolve(child));
	return rel === "" || !rel.startsWith("..") && !isAbsolute(rel);
}
//#endregion
//#region src/index.ts
const name = "dsh-session-manager";
/**
* Services are injected through a scoped `ctx.inject` in `apply` instead: in
* DSH 0.2.0 a plugin-level `webServer` injection is dropped again right after
* mount and the plugin is never re-applied.
*/
const inject = [];
const SCOPED_SERVICES = [
	"webServer",
	"sessionPersistence",
	"agents",
	"storageDomain",
	"loader"
];
/**
* Resolved lazily: in DSH 0.2.0 the registry activates late, and injecting it
* would keep this plugin from ever mounting.
*/
function workspaceRegistry(ctx) {
	const registry = ctx.get("workspaceRegistry");
	if (registry === void 0) throw new Error("workspace registry not ready");
	return registry;
}
/** DSH >= 0.2.0 lists snapshots (`{ header }`); older versions list bare headers. */
function compatHeader(item) {
	return item.header ?? item;
}
/** `locate` became private (but remains at runtime) in DSH 0.2.0. */
function locateSession(ctx, meta) {
	return ctx.sessionPersistence.locate?.(meta);
}
/**
* Subagent sessions reachable from one parent catalog, deepest first.
*
* The cascade runs before the parent, so a running descendant refuses the whole
* batch instead of leaving an orphan log behind. A composition without the
* subagent service — or a catalog that cannot be read — degrades to a
* parent-only delete, which is the behaviour this route had before the cascade.
*/
async function subagentDescendants(ctx, rootId) {
	let subagents;
	try {
		subagents = ctx.get("subagents");
	} catch {
		subagents = void 0;
	}
	if (subagents?.listDescendants === void 0) return {
		ok: true,
		ids: []
	};
	let rows;
	try {
		rows = await subagents.listDescendants(rootId);
	} catch (error) {
		ctx.logger.warn("[dsh-session-manager] descendant catalog unavailable; deleting the parent only:", error);
		return {
			ok: true,
			ids: []
		};
	}
	const children = rows.filter((row) => row.kind === "child").sort((a, b) => (b.depth ?? 0) - (a.depth ?? 0));
	if (children.some((row) => row.activity === "running")) return {
		ok: false,
		status: 409,
		error: "child-live"
	};
	return {
		ok: true,
		ids: children.map((row) => row.id)
	};
}
const ROUTE_PREFIX = "/dsh-session-manager";
const MAX_BODY_BYTES = 64 * 1024;
const SESSION_ID_RE = /^(session-)?[0-9a-fA-F-]+$/;
/** Maximum trash entries kept; the oldest overflow is purged automatically. */
const TRASH_LIMIT = 10;
function openFolderCommand(platform) {
	if (platform === "win32") return "explorer";
	if (platform === "darwin") return "open";
	return "xdg-open";
}
function openFolder(path, platform = process.platform) {
	return new Promise((resolve, reject) => {
		const child = spawn(openFolderCommand(platform), [path], {
			detached: true,
			stdio: "ignore"
		});
		child.once("error", reject);
		child.once("spawn", () => {
			child.unref();
			resolve();
		});
	});
}
const trashEntrySchema = z.object({
	sessionId: z.string(),
	cwd: z.string().optional(),
	originalPath: z.string().optional(),
	deletedAt: z.number()
});
/** The plugin's storage domain: trash entries plus the compaction threshold setting. */
const trashDomainSpec = defineDomain({
	name: "dsh_delete_session",
	version: 1,
	global: {
		schema: z.object({
			entries: z.array(trashEntrySchema),
			thresholdRatio: z.number().optional()
		}),
		initial: { entries: [] }
	},
	tables: {}
});
function trashRoot() {
	return dshHomePath("dsh-delete-session-trash");
}
function trashSessionDir(sessionId) {
	return join(trashRoot(), sessionId);
}
function readJsonBody(req) {
	return new Promise((resolve, reject) => {
		let data = "";
		req.on("data", (chunk) => {
			data += chunk;
			if (data.length > MAX_BODY_BYTES) {
				req.destroy();
				reject(/* @__PURE__ */ new Error("request body too large"));
			}
		});
		req.on("end", () => {
			if (data.length === 0) return resolve({});
			try {
				resolve(JSON.parse(data));
			} catch {
				reject(/* @__PURE__ */ new Error("invalid JSON body"));
			}
		});
		req.on("error", reject);
	});
}
function respond(res, status, payload) {
	const body = JSON.stringify(payload);
	res.writeHead(status, {
		"content-type": "application/json; charset=utf-8",
		"content-length": Buffer.byteLength(body)
	});
	res.end(body);
}
function parseSessionId(body) {
	const sessionId = body?.sessionId;
	if (typeof sessionId !== "string" || !SESSION_ID_RE.test(sessionId)) return void 0;
	return sessionId;
}
/** Optional `userSeq` of an undo request. */
function parseUserSeq(body) {
	const value = body?.userSeq;
	if (value === void 0) return void 0;
	return typeof value === "number" && Number.isInteger(value) && value >= 0 ? value : void 0;
}
/** Optional `messageId` of an undo request (a durable assistant message id). */
function parseMessageId(body) {
	const value = body?.messageId;
	if (typeof value !== "string" || value.length === 0 || value.length > 128) return void 0;
	return /^[A-Za-z0-9._:-]+$/.test(value) ? value : void 0;
}
/** Last real user message in a session's events. */
function lastUserSeq(events) {
	for (let index = events.length - 1; index >= 0; index--) {
		const event = events[index];
		if (event === void 0 || event.type !== "user/message") continue;
		if (event.data?.source?.kind === "user") return event.seq;
	}
}
/**
* The user message that started the turn of one finalized assistant message.
*
* @param events - the session's committed events.
* @param messageId - durable assistant message id from the Chat row.
* @returns the owning user message seq, or undefined when the message is unknown.
*/
function userSeqForMessage(events, messageId) {
	let cut;
	for (const event of events) {
		if (event.type !== "assistant/message") continue;
		const data = event.data;
		if (String(data?.message?.id) === messageId) {
			cut = event.seq;
			break;
		}
	}
	if (cut === void 0) return void 0;
	let found;
	for (const event of events) {
		if (event.seq >= cut) break;
		if (event.type !== "user/message") continue;
		if (event.data?.source?.kind === "user") found = event.seq;
	}
	return found;
}
/** Last `turn/end` before a sequence: the clean fork boundary for an undo. */
function turnEndBefore(events, target) {
	let boundary;
	for (const event of events) {
		if (event.seq >= target) break;
		if (event.type === "turn/end") boundary = event.seq;
	}
	return boundary;
}
/** User message sequences from one target through the end (the turns an undo unwinds). */
function userSeqsFrom(events, target) {
	const seqs = [];
	for (const event of events) {
		if (event.seq < target || event.type !== "user/message") continue;
		if (event.data?.source?.kind === "user") seqs.push(event.seq);
	}
	return seqs;
}
/** Resolve the active default preset through the official agent-presets service. */
function defaultPresetName(ctx) {
	const presets = ctx.get("agentPresets");
	if (typeof presets.defaultId !== "string" || presets.defaultId.length === 0) throw new Error("agent presets default id unavailable");
	return presets.defaultId;
}
/** Resolve the real composition path and trust instead of assuming a user path. */
async function resolvePresetComposition(ctx, name) {
	const preset = await ctx.get("agentPresets").resolve(name);
	if (typeof preset.path !== "string" || preset.path.length === 0) throw new Error(`agent preset composition path unavailable: ${name}`);
	if (preset.trust !== "system" && preset.trust !== "user") throw new Error(`agent preset trust unavailable: ${name}`);
	return {
		path: preset.path,
		trust: preset.trust
	};
}
/** Read `thresholdRatio` from the preset's compaction-basic block, if any. */
function parsePresetRatio(content) {
	const lines = content.split(/\r?\n/);
	const start = lines.findIndex((line) => /^\s*- id: compaction-basic\s*$/.test(line));
	if (start < 0) return void 0;
	for (let i = start + 1; i < lines.length; i++) {
		if (/^\s*- id: /.test(lines[i])) break;
		const match = lines[i].match(/^\s*thresholdRatio:\s*([0-9.]+)\s*$/);
		if (match !== null) return Number(match[1]);
	}
}
/**
* Update `thresholdRatio` inside the preset's `- id: compaction-basic` block:
* reuse the existing `config:`/`thresholdRatio:` lines or insert them with
* the block's indentation. Existing content and comments stay untouched.
*/
function upsertPresetRatio(content, newline, ratio) {
	const lines = content.split(/\r?\n/);
	const start = lines.findIndex((line) => /^\s*- id: compaction-basic\s*$/.test(line));
	if (start < 0) throw new Error("preset compaction-basic entry not found");
	const indentOf = (line) => (line.match(/^\s*/) ?? [""])[0];
	const base = indentOf(lines[start]);
	let end = lines.length;
	for (let i = start + 1; i < lines.length; i++) if (/^\s*- id: /.test(lines[i])) {
		end = i;
		break;
	}
	const configLine = `${base}  config:`;
	const ratioLine = `${base}    thresholdRatio: ${ratio}`;
	let configIdx = -1;
	for (let i = start + 1; i < end; i++) if (/^\s*config:\s*$/.test(lines[i])) {
		configIdx = i;
		break;
	}
	if (configIdx >= 0) {
		const configIndent = indentOf(lines[configIdx]);
		let ratioIdx = -1;
		for (let i = configIdx + 1; i < end; i++) {
			if (/^\s*thresholdRatio:/.test(lines[i])) {
				ratioIdx = i;
				break;
			}
			if (indentOf(lines[i]).length <= configIndent.length && /^\S/.test(lines[i])) break;
		}
		if (ratioIdx >= 0) lines[ratioIdx] = `${configIndent}  thresholdRatio: ${ratio}`;
		else lines.splice(configIdx + 1, 0, `${configIndent}  thresholdRatio: ${ratio}`);
	} else lines.splice(end, 0, configLine, ratioLine);
	return lines.join(newline);
}
/** Read the preset file, atomically write the updated content back. */
async function writePresetComposition(path, ratio) {
	let content;
	try {
		content = await readFile(path, "utf8");
	} catch (error) {
		if (error.code !== "ENOENT") throw error;
		throw new Error(`preset composition file not found: ${path}`);
	}
	const newline = content.includes("\r\n") ? "\r\n" : "\n";
	let next = upsertPresetRatio(content, newline, ratio);
	if (!next.endsWith(newline)) next += newline;
	const tmp = `${path}.tmp`;
	await writeFile(tmp, next, "utf8");
	await rename(tmp, path);
}
/**
* Sync the WorkspaceRegistry's private state cache with the durable domain
* value. There is no public unarchive API; writing the domain directly leaves
* the registry's cached state stale, so the next archiveSession() call would
* idempotently skip on the old value. This pokes the private field to keep
* both in lockstep. Fragile against a DSH upgrade, but the alternative is
* silent un-archives/archives that disagree with what clients see.
*/
function syncRegistryState(ctx, next) {
	const registry = ctx.get("workspaceRegistry");
	if (registry !== void 0 && "state" in registry) registry.state = next;
}
/** Remove one session id from the workspace archive set through the domain. */
async function unarchive(ctx, sessionId) {
	const workspace = ctx.storageDomain.get("workspace");
	if (workspace === void 0) return;
	const state = workspace.global.get();
	if (!state.archivedSessionIds.includes(sessionId)) return;
	const next = {
		...state,
		archivedSessionIds: state.archivedSessionIds.filter((id) => id !== sessionId)
	};
	await workspace.global.set(next);
	syncRegistryState(ctx, next);
}
/**
* Apply a new threshold to the compaction engines of already-open sessions.
* Sessions using the same preset share one engine in the preset's isolated
* realm; the agentPresets service's `serviceFor` is the official channel
* that reaches it (called on the HOST's service instance, so module state is
* shared). The engine reads `this.config` at every decision, so updating the
* resolved threshold field takes effect immediately. Best-effort: failures
* only warn.
*/
async function applyThresholdToLiveAgents(ctx, ratio) {
	try {
		const presets = ctx.get("agentPresets");
		if (presets?.serviceFor === void 0) return;
		const headers = (await ctx.sessionPersistence.list()).map(compatHeader);
		for (const header of headers) {
			const agent = ctx.agents.get(header.id);
			if (agent === void 0) continue;
			const engine = presets.serviceFor(agent, "compaction");
			if (engine === void 0 || engine.config === void 0) continue;
			engine.config.thresholdRatio = ratio;
		}
	} catch (error) {
		ctx.logger.warn("[dsh-session-manager] live-agent threshold update failed:", error);
	}
}
function setup(ctx) {
	return ctx.storageDomain.open(trashDomainSpec).then((trash) => {
		if (ctx.fiber?.uid === null) {
			Promise.resolve(trash.close()).catch((error) => {
				ctx.logger.warn("[dsh-session-manager] trash close failed:", error);
			});
			return async () => {};
		}
		const routeDisposers = [];
		const registerRoute = (route) => {
			routeDisposers.push(ctx.webServer.register(route));
		};
		const getEntries = () => trash.global.get().entries;
		const setEntries = (entries) => {
			const current = trash.global.get();
			return trash.global.set({
				...current,
				entries
			}).catch((error) => {
				ctx.logger.warn("[dsh-session-manager] trash persist failed:", error);
				throw error;
			});
		};
		let mutationTail = Promise.resolve();
		const withMutationLock = (operation) => {
			const result = mutationTail.then(operation, operation);
			mutationTail = result.then(() => void 0, () => void 0);
			return result;
		};
		let configuredThreshold = trash.global.get().thresholdRatio ?? null;
		const setConfiguredThreshold = async (ratio) => {
			const current = trash.global.get();
			await trash.global.set({
				...current,
				thresholdRatio: ratio
			}).catch((error) => {
				ctx.logger.warn("[dsh-session-manager] threshold persist failed:", error);
				throw error;
			});
			configuredThreshold = ratio;
		};
		{
			const presets = ctx.get("agentPresets");
			ctx.on("agent/pre-step", async ({ agent }, next) => {
				try {
					if (configuredThreshold !== null && presets?.serviceFor !== void 0) {
						const engine = presets.serviceFor(agent, "compaction");
						if (engine?.config !== void 0 && engine.config.thresholdRatio !== configuredThreshold) engine.config.thresholdRatio = configuredThreshold;
					}
				} catch {}
				return next();
			}, { prepend: true });
		}
		const snapshotStore = dshHomePath("dsh-session-manager-snapshots");
		const trackers = /* @__PURE__ */ new Map();
		const trackerFor = (sessionId, cwd) => {
			const existing = trackers.get(sessionId);
			if (existing !== void 0) return existing;
			const tracker = new WorkspaceSnapshots({
				sessionId,
				cwd,
				storeRoot: snapshotStore,
				logger: ctx.logger
			});
			trackers.set(sessionId, tracker);
			return tracker;
		};
		/**
		* Optional `sessions` / `sessionController` lookups.
		*
		* Both stay OUT of `SCOPED_SERVICES`: this plugin must keep mounting in a
		* composition without them, and undo simply reports itself unavailable.
		*/
		const liveSessions = () => {
			try {
				return ctx.get("sessions");
			} catch {
				return;
			}
		};
		const sessionController = () => {
			try {
				return ctx.get("sessionController");
			} catch {
				return;
			}
		};
		/** The tail of one live session's events: a whole turn fits in this window. */
		const recentEvents = (session) => session.snapshotEvents(Math.max(0, Number(session.seq) - 500)).map((event) => ({
			seq: event.seq,
			type: event.type,
			data: event.data
		}));
		if (liveSessions() !== void 0) ctx.on("tools/execute", async (exec, next) => {
			const agent = exec.agent;
			if (agent === void 0 || exec.parent !== void 0) return next();
			const live = liveSessions()?.get(String(agent.id));
			if (live === void 0) return next();
			return trackerFor(String(agent.id), live.header.cwd).around(exec, next, () => recentEvents(live));
		});
		/**
		* Archive one session and make sure the client archive set carries its id.
		*
		* @param id - session to archive.
		* @returns whether it was already archived, or the failure code.
		*/
		const archiveOne = async (id) => {
			const workspace = ctx.storageDomain.get("workspace");
			const wasArchived = workspace !== void 0 && workspace.global.get().archivedSessionIds.includes(id);
			try {
				await workspaceRegistry(ctx).archiveSession(id);
			} catch (error) {
				ctx.logger.warn(`[dsh-session-manager] archive failed for ${id}:`, error);
				return {
					ok: false,
					error: "archive-failed"
				};
			}
			try {
				const currentWorkspace = ctx.storageDomain.get("workspace");
				if (currentWorkspace !== void 0) {
					const current = currentWorkspace.global.get();
					if (!current.archivedSessionIds.includes(id)) {
						const next = {
							...current,
							archivedSessionIds: [...current.archivedSessionIds, id]
						};
						await currentWorkspace.global.set(next);
						syncRegistryState(ctx, next);
						ctx.logger.debug(`[dsh-session-manager] patched archived set for ${id} (stale registry cache)`);
					}
				}
			} catch (error) {
				ctx.logger.warn(`[dsh-session-manager] archived-set patch failed for ${id}:`, error);
				return {
					ok: false,
					error: "archive-failed"
				};
			}
			return {
				ok: true,
				wasArchived
			};
		};
		/**
		* Archive one session and move its artifact into the trash.
		*
		* Shared by the subagent cascade and the parent: one archive/move/record
		* implementation and one rollback, so a child and a parent are trashed
		* exactly alike.
		*
		* @param id - session to trash.
		* @param headers - persistence headers read once per delete batch.
		* @returns success, or an HTTP status plus a stable error code.
		*/
		const trashOne = async (id, headers) => {
			const meta = headers.find((header) => header.id === id);
			const agent = ctx.agents.get(id);
			const live = agent !== void 0;
			if (agent?.status === "running") return {
				ok: false,
				status: 409,
				error: "session-live"
			};
			let originalPath;
			if (meta !== void 0) {
				const location = locateSession(ctx, meta);
				if (location === void 0) return {
					ok: false,
					status: 500,
					error: "no-artifact-location"
				};
				originalPath = dirname(location.path);
			}
			let wasArchived = false;
			const trashPath = trashSessionDir(id);
			let archiveStarted = false;
			let artifactMoved = false;
			let failureCode = "delete-failed";
			try {
				failureCode = "archive-failed";
				archiveStarted = true;
				const archived = await archiveOne(id);
				wasArchived = archived.ok ? archived.wasArchived : false;
				if (!archived.ok) return {
					ok: false,
					status: 500,
					error: archived.error
				};
				failureCode = "delete-failed";
				if (!live && originalPath !== void 0 && existsSync(originalPath)) {
					await mkdir(trashRoot(), { recursive: true });
					await rm(trashPath, {
						recursive: true,
						force: true
					});
					await rename(originalPath, trashPath);
					artifactMoved = true;
					ctx.logger.debug(`[dsh-session-manager] moved ${id} artifact to trash`);
				}
				const entries = getEntries();
				const existingIndex = entries.findIndex((entry) => entry.sessionId === id);
				let next;
				let overflow = [];
				if (existingIndex >= 0) next = entries.map((entry, index) => index === existingIndex ? {
					...entry,
					deletedAt: Date.now()
				} : entry);
				else {
					next = [...entries, {
						sessionId: id,
						cwd: meta?.cwd,
						originalPath,
						deletedAt: Date.now()
					}];
					if (next.length > 10) {
						overflow = next.slice(0, next.length - 10);
						next = next.slice(next.length - 10);
					}
				}
				await setEntries(next);
				for (const entry of overflow) await rm(trashSessionDir(entry.sessionId), {
					recursive: true,
					force: true
				}).catch(() => {});
				return { ok: true };
			} catch (error) {
				if (artifactMoved && originalPath !== void 0 && existsSync(trashPath) && !existsSync(originalPath)) try {
					await mkdir(dirname(originalPath), { recursive: true });
					await rename(trashPath, originalPath);
				} catch (rollbackError) {
					ctx.logger.warn(`[dsh-session-manager] artifact rollback failed for ${id}:`, rollbackError);
				}
				if (archiveStarted && !wasArchived) try {
					await unarchive(ctx, id);
				} catch (rollbackError) {
					ctx.logger.warn(`[dsh-session-manager] archive rollback failed for ${id}:`, rollbackError);
				}
				ctx.logger.warn(`[dsh-session-manager] ${failureCode} for ${id}:`, error);
				return {
					ok: false,
					status: 500,
					error: failureCode
				};
			}
		};
		try {
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/delete`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						await withMutationLock(async () => {
							if (ctx.agents.get(id)?.status === "running") {
								respond(res, 409, {
									ok: false,
									error: "session-live"
								});
								return;
							}
							const descendants = await subagentDescendants(ctx, id);
							if (!descendants.ok) {
								respond(res, descendants.status, {
									ok: false,
									error: descendants.error
								});
								return;
							}
							const headers = (await ctx.sessionPersistence.list()).map(compatHeader);
							for (const childId of descendants.ids) {
								const child = await trashOne(childId, headers);
								if (!child.ok) {
									respond(res, child.status, {
										ok: false,
										error: child.error
									});
									return;
								}
							}
							const outcome = await trashOne(id, headers);
							if (!outcome.ok) {
								respond(res, outcome.status, {
									ok: false,
									error: outcome.error
								});
								return;
							}
							respond(res, 200, { ok: true });
						});
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] delete failed:", error);
						respond(res, 500, {
							ok: false,
							error: "delete-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/undo`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					if (body.userSeq !== void 0 && parseUserSeq(body) === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-user-seq"
					});
					if (body.messageId !== void 0 && parseMessageId(body) === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-message-id"
					});
					const requestedUserSeq = parseUserSeq(body);
					const requestedMessageId = parseMessageId(body);
					const controller = sessionController();
					if (controller === void 0) return respond(res, 500, {
						ok: false,
						error: "controller-unavailable"
					});
					try {
						await withMutationLock(async () => {
							if (ctx.agents.get(id)?.status === "running") {
								respond(res, 409, {
									ok: false,
									error: "session-live"
								});
								return;
							}
							const live = liveSessions()?.get(String(id));
							if (live !== void 0) await liveSessions()?.flush(live).catch((error) => {
								ctx.logger.warn(`[dsh-session-manager] flush before undo failed for ${id}:`, error);
							});
							let inspection;
							const abort = new AbortController();
							const timer = setTimeout(() => abort.abort(), 15e3);
							try {
								inspection = await controller.inspect(String(id), abort.signal);
							} catch (error) {
								ctx.logger.warn(`[dsh-session-manager] inspect before undo failed for ${id}:`, error);
								respond(res, 500, {
									ok: false,
									error: "inspect-failed"
								});
								return;
							} finally {
								clearTimeout(timer);
							}
							const events = inspection.events.map((event) => ({
								seq: event.seq,
								type: event.type,
								data: event.data
							}));
							const target = requestedUserSeq ?? (requestedMessageId === void 0 ? void 0 : userSeqForMessage(events, requestedMessageId)) ?? lastUserSeq(events);
							if (target === void 0) {
								respond(res, 400, {
									ok: false,
									error: requestedMessageId === void 0 ? "no-user-message" : "message-not-found"
								});
								return;
							}
							const boundary = turnEndBefore(events, target);
							const opId = `undo:${id}:${target}:${Date.now()}`;
							const tracker = trackerFor(String(id), inspection.meta.cwd);
							let restored;
							try {
								restored = await tracker.restore(userSeqsFrom(events, target), opId);
							} catch (error) {
								ctx.logger.warn(`[dsh-session-manager] workspace rollback failed for ${id}:`, error);
								respond(res, 500, {
									ok: false,
									error: "workspace-rollback-failed"
								});
								return;
							}
							let forked = true;
							let nextSessionId;
							try {
								nextSessionId = boundary === void 0 ? String((await controller.create({ cwd: inspection.meta.cwd })).sessionId) : String((await controller.fork({
									sessionId: String(id),
									atSeq: boundary
								})).sessionId);
								if (boundary === void 0) forked = false;
							} catch (error) {
								ctx.logger.warn(`[dsh-session-manager] fork for undo failed for ${id}:`, error);
								await tracker.rollback(opId).catch((rollbackError) => {
									ctx.logger.warn(`[dsh-session-manager] undo compensation failed for ${id}:`, rollbackError);
								});
								respond(res, 500, {
									ok: false,
									error: "fork-failed"
								});
								return;
							}
							const archived = await archiveOne(id);
							if (!archived.ok) {
								await tracker.rollback(opId).catch((rollbackError) => {
									ctx.logger.warn(`[dsh-session-manager] undo compensation failed for ${id}:`, rollbackError);
								});
								respond(res, 500, {
									ok: false,
									error: archived.error
								});
								return;
							}
							await tracker.commit(opId).catch((error) => {
								ctx.logger.warn(`[dsh-session-manager] redo bookkeeping failed for ${id}:`, error);
							});
							respond(res, 200, {
								ok: true,
								sessionId: nextSessionId,
								files: restored.files,
								forked,
								...restored.warning === void 0 ? {} : { warning: restored.warning }
							});
						});
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] undo failed:", error);
						respond(res, 500, {
							ok: false,
							error: "undo-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/restore`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						await withMutationLock(async () => {
							const entries = getEntries();
							const entry = entries.find((candidate) => candidate.sessionId === id);
							if (entry === void 0) {
								const meta = (await ctx.sessionPersistence.list()).map(compatHeader).find((header) => header.id === id);
								const agent = ctx.agents.get(id);
								if (meta === void 0 && agent === void 0) return respond(res, 404, {
									ok: false,
									error: "trash-entry-not-found"
								});
								await unarchive(ctx, id);
								ctx.logger.debug(`[dsh-session-manager] restore ${id}: no trash entry, un-archived only`);
								return respond(res, 200, { ok: true });
							}
							const from = trashSessionDir(id);
							if (existsSync(from)) {
								if (entry.originalPath === void 0) {
									ctx.logger.warn(`[dsh-session-manager] restore ${id}: artifact exists in trash but entry has no original path`);
									return respond(res, 500, {
										ok: false,
										error: "no-original-path"
									});
								}
								if (existsSync(entry.originalPath)) {
									await rm(from, {
										recursive: true,
										force: true
									});
									ctx.logger.warn(`[dsh-session-manager] restore ${id}: original path already exists, discarding trash copy`);
								} else {
									await mkdir(dirname(entry.originalPath), { recursive: true });
									await rename(from, entry.originalPath);
									ctx.logger.debug(`[dsh-session-manager] restored ${id} artifact from trash`);
								}
							} else ctx.logger.debug(`[dsh-session-manager] restore ${id}: no artifact in trash (live or blank session)`);
							await unarchive(ctx, id);
							await setEntries(entries.filter((candidate) => candidate.sessionId !== id));
							respond(res, 200, { ok: true });
						});
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] restore failed:", error);
						respond(res, 500, {
							ok: false,
							error: "restore-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/purge`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						await withMutationLock(async () => {
							const entries = getEntries();
							const entry = entries.find((candidate) => candidate.sessionId === id);
							if (entry === void 0) {
								respond(res, 404, {
									ok: false,
									error: "trash-entry-not-found"
								});
								return;
							}
							await rm(trashSessionDir(id), {
								recursive: true,
								force: true
							});
							if (entry.originalPath !== void 0) await rm(entry.originalPath, {
								recursive: true,
								force: true
							});
							await setEntries(entries.filter((candidate) => candidate.sessionId !== id));
							respond(res, 200, { ok: true });
						});
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] purge failed:", error);
						respond(res, 500, {
							ok: false,
							error: "purge-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/pause`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						const agent = ctx.agents.get(id);
						if (agent === void 0) return respond(res, 404, {
							ok: false,
							error: "agent-not-found"
						});
						agent.cancel({ kind: "user" });
						respond(res, 200, { ok: true });
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] pause failed:", error);
						respond(res, 500, {
							ok: false,
							error: "pause-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/stats`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						const handle = await ctx.sessionPersistence.open(id, "read");
						try {
							const { events } = await handle.read();
							const wanted = /* @__PURE__ */ new Set([
								"turn/start",
								"user/message",
								"assistant/message",
								"tool/call"
							]);
							respond(res, 200, {
								ok: true,
								entries: events.filter((event) => wanted.has(event.type)).slice(-5e3).map((event) => ({
									type: event.type,
									time: event.time,
									name: event.type === "tool/call" ? event.data.name : void 0
								}))
							});
						} finally {
							await handle.close();
						}
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] stats failed:", error);
						respond(res, 500, {
							ok: false,
							error: "stats-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/trash`,
				handler: async (_req, res) => {
					try {
						respond(res, 200, {
							ok: true,
							entries: getEntries(),
							limit: 10
						});
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] trash list failed:", error);
						respond(res, 500, {
							ok: false,
							error: "trash-list-failed"
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/compaction-threshold`,
				handler: async (req, res) => {
					if (req.method === "GET") {
						let ratio = configuredThreshold;
						if (ratio === null) try {
							ratio = parsePresetRatio(await readFile((await resolvePresetComposition(ctx, defaultPresetName(ctx))).path, "utf8")) ?? .8;
						} catch {
							ratio = .8;
						}
						respond(res, 200, {
							ok: true,
							ratio
						});
						return;
					}
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const ratio = body?.ratio;
					if (typeof ratio !== "number" || !Number.isFinite(ratio) || ratio < .17 || ratio > .9) return respond(res, 400, {
						ok: false,
						error: "invalid-ratio"
					});
					try {
						await withMutationLock(async () => {
							await setConfiguredThreshold(ratio);
							try {
								const preset = await resolvePresetComposition(ctx, defaultPresetName(ctx));
								if (preset.trust !== "system") await writePresetComposition(preset.path, ratio);
							} catch (error) {
								ctx.logger.debug("[dsh-session-manager] preset file not updated:", error);
							}
							await applyThresholdToLiveAgents(ctx, ratio);
							respond(res, 200, { ok: true });
						});
					} catch (error) {
						const message = error instanceof Error ? error.message : String(error);
						ctx.logger.warn("[dsh-session-manager] compaction-threshold update failed:", error);
						respond(res, 500, {
							ok: false,
							error: message
						});
					}
				}
			});
			registerRoute({
				kind: "exact",
				path: `${ROUTE_PREFIX}/open-folder`,
				handler: async (req, res) => {
					if (req.method !== "POST") return respond(res, 405, {
						ok: false,
						error: "method-not-allowed"
					});
					let body;
					try {
						body = await readJsonBody(req);
					} catch {
						return respond(res, 400, {
							ok: false,
							error: "bad-request"
						});
					}
					const id = parseSessionId(body);
					if (id === void 0) return respond(res, 400, {
						ok: false,
						error: "invalid-session-id"
					});
					try {
						let dir;
						const meta = (await ctx.sessionPersistence.list()).map(compatHeader).find((header) => header.id === id);
						if (meta !== void 0) {
							const location = locateSession(ctx, meta);
							if (location !== void 0) dir = dirname(location.path);
						}
						if (dir === void 0 || !existsSync(dir)) {
							const entry = getEntries().find((candidate) => candidate.sessionId === id);
							if (entry?.originalPath !== void 0 && existsSync(entry.originalPath)) dir = entry.originalPath;
						}
						if (dir === void 0 || !existsSync(dir)) return respond(res, 404, {
							ok: false,
							error: "folder-not-found"
						});
						await openFolder(dir);
						respond(res, 200, { ok: true });
					} catch (error) {
						ctx.logger.warn("[dsh-session-manager] open-folder failed:", error);
						respond(res, 500, {
							ok: false,
							error: "open-folder-failed"
						});
					}
				}
			});
			return async () => {
				for (let i = routeDisposers.length - 1; i >= 0; i--) try {
					routeDisposers[i]();
				} catch (error) {
					ctx.logger.warn("[dsh-session-manager] route dispose failed:", error);
				}
				await trash.close();
			};
		} catch (error) {
			for (let i = routeDisposers.length - 1; i >= 0; i--) try {
				routeDisposers[i]();
			} catch {}
			Promise.resolve(trash.close()).catch((closeError) => {
				ctx.logger.warn("[dsh-session-manager] trash close after failed setup:", closeError);
			});
			throw error;
		}
	});
}
function apply(ctx) {
	ctx.inject(SCOPED_SERVICES, (scoped) => {
		const ready = setup(scoped);
		scoped.effect(() => () => ready.then((dispose) => dispose()).catch((error) => {
			scoped.logger?.warn?.("[dsh-session-manager] scoped setup failed:", error);
		}), "dsh-session-manager");
	});
}
//#endregion
export { TRASH_LIMIT, apply, inject, name, openFolderCommand };
