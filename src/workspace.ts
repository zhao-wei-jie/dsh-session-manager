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

import { execFile } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdir, readFile, rename, rm, stat, writeFile } from 'node:fs/promises'
import { isAbsolute, join, relative, resolve } from 'node:path'
import { promisify } from 'node:util'
import type { ToolDispatchExecution, ToolExecutionResult } from '@deepseek-ai/dsh-tools'

const execFileAsync = promisify(execFile)
/** Untracked files larger than this stay out of snapshots. */
const MAX_UNTRACKED_BYTES = 2 * 1024 * 1024
/** Turns retained per session; older patches are dropped. */
const MAX_RETAINED_TURNS = 50
const STATE_VERSION = 1

/** One root tool call's pre-image and the files it changed. */
interface WorkspacePatch {
  /** Sequence of the tool call, used to order patches within a turn. */
  callSeq: number
  /** Tree captured before the call. */
  before: string
  /** Files that differ after the call. */
  files: string[]
}

/** The workspace state captured immediately before an undo. */
interface WorkspaceRedo {
  tree: string
  files: string[]
}

/** One file restored to one tree. */
interface WorkspaceTarget {
  file: string
  tree: string
}

/** Journal entry of an undo whose files were written but not yet committed. */
interface PendingOperation {
  opId: string
  rollback: WorkspaceRedo
  target: WorkspaceTarget[]
}

interface PersistedState {
  version: typeof STATE_VERSION
  /** Patches grouped by the user message sequence that started the turn. */
  patches: Record<string, WorkspacePatch[]>
  /** Pre-undo workspace per undo operation id. */
  redos: Record<string, WorkspaceRedo>
  pending?: PendingOperation
}

/** The minimal session-event shape this module reads. */
export interface WorkspaceEvent {
  readonly seq: number
  readonly type: string
  readonly data?: unknown
}

/** Snapshot outcome of one undo: restored file count, or why nothing was restored. */
export interface WorkspaceRestoreResult {
  files: number
  warning?: string
}

/** Construction options for one session's tracker. */
export interface WorkspaceSnapshotsOptions {
  /** Session whose workspace is mirrored. */
  sessionId: string
  /** The session's project directory at the time the tracker was created. */
  cwd: string | undefined
  /** Store root (`<dshHome>/dsh-session-manager/snapshots`). */
  storeRoot: string
  /** Diagnostics sink; snapshot failures must never reach the model. */
  logger: { warn(message: string, cause?: unknown): void }
}

/** A missing or unusable git workspace, as a user-facing warning. */
const GIT_MISSING_TEXT = '工作区快照不可用(未找到 git 仓库或 git 命令),本次只回退了对话。'

/**
 * One session's hidden-git workspace checkpoints.
 *
 * All git work is serialized: the runtime dispatches parallel tool calls, and a
 * hidden repository cannot take two `write-tree` writers at once.
 */
export class WorkspaceSnapshots {
  private root: string | undefined
  private gitDir: string | undefined
  private unavailable: string | undefined
  private initPromise: Promise<boolean> | undefined
  private loaded = false
  private state: PersistedState = { version: STATE_VERSION, patches: {}, redos: {} }
  private gitTail: Promise<void> = Promise.resolve()
  private stateTail: Promise<void> = Promise.resolve()

  constructor(private readonly options: WorkspaceSnapshotsOptions) {}

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
  async around(
    exec: ToolDispatchExecution,
    next: () => Promise<ToolExecutionResult>,
    events: () => readonly WorkspaceEvent[],
  ): Promise<ToolExecutionResult> {
    if (exec.parent !== undefined) return next()
    const callId = String(exec.rootCallId)
    let userSeq: number | undefined
    let before: string | undefined
    try {
      userSeq = userSeqForCall(events(), callId)
      if (userSeq !== undefined) before = await this.snapshot()
    } catch (error) {
      this.options.logger.warn('[dsh-session-manager] workspace snapshot before the tool call failed:', error)
    }
    let result: ToolExecutionResult
    try {
      result = await next()
    } finally {
      if (userSeq !== undefined && before !== undefined) {
        try {
          await this.recordCallPatches(userSeq, callId, before, events())
        } catch (error) {
          this.options.logger.warn('[dsh-session-manager] workspace snapshot after the tool call failed:', error)
        }
      }
    }
    return result
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
  async restore(userSeqs: readonly number[], opId: string): Promise<WorkspaceRestoreResult> {
    if (!await this.initialize()) return { files: 0, warning: this.unavailable ?? GIT_MISSING_TEXT }
    await this.recoverPending()

    const patches = [...new Set(userSeqs)]
      .flatMap((seq) => this.state.patches[String(seq)] ?? [])
      .sort((a, b) => a.callSeq - b.callSeq)
    if (patches.length === 0) return { files: 0 }

    const current = await this.snapshot()
    if (current === undefined) return { files: 0, warning: this.unavailable ?? GIT_MISSING_TEXT }

    // Earliest pre-image per file: later patches of the same file are already
    // covered by unwinding to the first one.
    const firstByFile = new Map<string, string>()
    for (const patch of patches) {
      for (const file of patch.files) {
        if (firstByFile.has(file)) continue
        if (await this.isExcludedCurrentFile(file)) continue
        firstByFile.set(file, patch.before)
      }
    }
    if (firstByFile.size === 0) return { files: 0 }

    const target: WorkspaceTarget[] = [...firstByFile].map(([file, tree]) => ({ file, tree }))
    const rollback: WorkspaceRedo = { tree: current, files: [...firstByFile.keys()] }
    this.state.pending = { opId, rollback, target }
    await this.persistState()
    try {
      await this.restoreTargets(target)
    } catch (error) {
      await this.restoreRedo(rollback).catch((rollbackError) => {
        this.options.logger.warn('[dsh-session-manager] workspace compensation failed:', rollbackError)
      })
      this.state.pending = undefined
      await this.persistState().catch(() => {})
      throw error
    }
    return { files: target.length }
  }

  /**
   * Mark an undo as applied: its pre-undo tree becomes the redo entry.
   *
   * @param opId - operation id handed to {@link restore}.
   */
  async commit(opId: string): Promise<void> {
    const pending = this.state.pending
    if (pending === undefined || pending.opId !== opId) return
    this.state.redos[opId] = pending.rollback
    this.state.pending = undefined
    await this.persistState()
  }

  /**
   * Undo one {@link restore} that could not be completed: put the files back to
   * the pre-undo tree.
   *
   * @param opId - operation id handed to {@link restore}.
   */
  async rollback(opId: string): Promise<void> {
    const pending = this.state.pending
    if (pending === undefined || pending.opId !== opId) return
    await this.restoreRedo(pending.rollback)
    this.state.pending = undefined
    await this.persistState()
  }

  /**
   * Re-apply the pre-undo tree recorded by an earlier {@link commit}.
   *
   * @param opId - operation id of the undo to reverse.
   * @returns restored file count.
   */
  async redo(opId: string): Promise<WorkspaceRestoreResult> {
    if (!await this.initialize()) return { files: 0, warning: this.unavailable ?? GIT_MISSING_TEXT }
    await this.recoverPending()
    const redo = this.state.redos[opId]
    if (redo === undefined) return { files: 0 }
    await this.restoreRedo(redo)
    delete this.state.redos[opId]
    await this.persistState()
    return { files: redo.files.length }
  }

  /**
   * Record one call's changed files, keyed by the turn it belongs to.
   *
   * @param userSeq - user message that started the turn.
   * @param callId - root tool call identity.
   * @param before - tree captured before the call.
   * @param events - committed events read after the call.
   */
  private async recordCallPatches(
    userSeq: number,
    callId: string,
    before: string,
    events: readonly WorkspaceEvent[],
  ): Promise<void> {
    const after = await this.snapshot()
    if (after === undefined || after === before) return
    const files = await this.changedFiles(before, after)
    if (files.length === 0) return
    const callSeq = callSeqForCall(events, callId) ?? Number.MAX_SAFE_INTEGER
    const key = String(userSeq)
    const list = this.state.patches[key] ?? []
    list.push({ callSeq, before, files })
    this.state.patches[key] = list
    this.pruneTurns()
    await this.persistState()
  }

  /** Drop the oldest turns once the per-session budget is exceeded. */
  private pruneTurns(): void {
    const keys = Object.keys(this.state.patches)
    if (keys.length <= MAX_RETAINED_TURNS) return
    keys
      .map(Number)
      .sort((a, b) => a - b)
      .slice(0, keys.length - MAX_RETAINED_TURNS)
      .forEach((seq) => delete this.state.patches[String(seq)])
  }

  /** Compensate an operation interrupted between its journal write and commit. */
  private async recoverPending(): Promise<void> {
    const pending = this.state.pending
    if (pending === undefined) return
    try {
      await this.restoreRedo(pending.rollback)
      this.options.logger.warn('[dsh-session-manager] recovered an interrupted workspace undo; files were restored to the pre-undo state')
    } catch (error) {
      this.options.logger.warn('[dsh-session-manager] could not recover an interrupted workspace undo:', error)
    }
    this.state.pending = undefined
    await this.persistState().catch(() => {})
  }

  /** Resolve the workspace root and open (or create) the hidden repository. */
  private initialize(): Promise<boolean> {
    if (this.initPromise !== undefined) return this.initPromise
    this.initPromise = this.initializeOnce()
    return this.initPromise
  }

  private async initializeOnce(): Promise<boolean> {
    const cwd = this.options.cwd
    if (cwd === undefined || cwd === '') {
      this.unavailable = '会话没有工作目录,本次只回退了对话。'
      return false
    }
    try {
      let root: string
      try {
        const { stdout } = await execFileAsync('git', ['-C', cwd, 'rev-parse', '--show-toplevel'], { encoding: 'utf8' })
        root = resolve(stdout.trim())
      } catch (error) {
        // Not inside any repository: give the workspace its own repository so
        // snapshots keep working (the user-facing decision: auto `git init`).
        if (isDriveRoot(resolve(cwd))) {
          this.unavailable = '工作目录是盘符根目录,为安全起见不做文件快照,本次只回退了对话。'
          return false
        }
        await execFileAsync('git', ['-C', cwd, 'init', '-q'], { encoding: 'utf8' })
        this.options.logger.warn(`[dsh-session-manager] 工作区不是 git 仓库,已自动执行 git init:${cwd}`)
        const retry = await execFileAsync('git', ['-C', cwd, 'rev-parse', '--show-toplevel'], { encoding: 'utf8' })
        root = resolve(retry.stdout.trim())
      }
      if (isInside(this.options.storeRoot, root)) {
        // The mirror would snapshot its own objects and corrupt itself.
        this.unavailable = '工作区快照目录位于当前仓库内,已跳过文件回退,本次只回退了对话。'
        return false
      }
      this.root = root
      const key = createHash('sha256')
        .update(root)
        .update('\0')
        .update(String(this.options.sessionId))
        .digest('hex')
        .slice(0, 24)
      this.gitDir = join(this.options.storeRoot, key)
      await mkdir(this.gitDir, { recursive: true })
      try {
        await this.git(['rev-parse', '--is-bare-repository'])
      } catch {
        await execFileAsync('git', ['init', '--bare', this.gitDir], { encoding: 'utf8' })
        await this.git(['config', 'core.autocrlf', 'false'])
        await this.git(['config', 'core.longpaths', 'true'])
      }
      await this.loadState()
      return true
    } catch (error) {
      this.unavailable = `工作区快照不可用(${error instanceof Error ? error.message : String(error)}),本次只回退了对话。`
      return false
    }
  }

  /** Mirror the current tracked + untracked workspace into one tree. */
  private async snapshot(): Promise<string | undefined> {
    if (!await this.initialize()) return undefined
    return this.serialGit(async () => {
      const tracked = this.splitPaths(await this.sourceGit(['ls-files', '-z', '--cached', '--', '.']))
      const untracked = this.splitPaths(await this.sourceGit(['ls-files', '-z', '--others', '--exclude-standard', '--', '.']))
      const allowed: string[] = []
      for (const file of untracked) {
        try {
          const info = await stat(join(this.requireRoot(), file))
          if (!info.isFile() || info.size <= MAX_UNTRACKED_BYTES) allowed.push(file)
        } catch {
          // Vanished between listing and stat: skip it.
        }
      }
      const candidates = [...new Set([...tracked, ...allowed])]
      for (const batch of this.pathBatches(candidates)) {
        await this.git(['add', '--all', '--', ...batch.map((file) => `:(top,literal)${file}`)])
      }
      const candidateSet = new Set(candidates)
      const hidden = this.splitPaths(await this.git(['ls-files', '-z']))
      const deleted = hidden.filter((file) => !candidateSet.has(file))
      for (const batch of this.pathBatches(deleted)) {
        await this.git(['rm', '--cached', '-f', '--ignore-unmatch', '--', ...batch.map((file) => `:(top,literal)${file}`)])
      }
      return (await this.git(['write-tree'])).trim()
    })
  }

  /** Files whose content differs between two trees, minus ignored/oversized ones. */
  private async changedFiles(before: string, after: string): Promise<string[]> {
    const output = await this.serialGit(() => this.git(['diff', '--name-only', '-z', before, after, '--', '.']))
    const filtered: string[] = []
    for (const file of output.split('\0').filter(Boolean)) {
      if (!await this.isExcludedCurrentFile(file)) filtered.push(file)
    }
    return filtered
  }

  /** Whether a path is ignored now and not tracked, or an oversized untracked file. */
  private async isExcludedCurrentFile(file: string): Promise<boolean> {
    const root = this.requireRoot()
    try {
      await execFileAsync('git', ['-C', root, 'check-ignore', '--no-index', '--quiet', '--', file], { encoding: 'utf8' })
      return true
    } catch (error) {
      if ((error as { code?: unknown }).code !== 1) throw error
    }
    try {
      await execFileAsync('git', ['-C', root, 'ls-files', '--error-unmatch', '--', file], { encoding: 'utf8' })
      return false
    } catch (error) {
      if ((error as { code?: unknown }).code !== 1) throw error
    }
    try {
      const info = await stat(join(root, file))
      return info.isFile() && info.size > MAX_UNTRACKED_BYTES
    } catch {
      return false
    }
  }

  /** Restore one file (or delete it when the tree does not contain it). */
  private async restoreFile(tree: string, file: string): Promise<void> {
    const literal = `:(top,literal)${file}`
    const listed = await this.serialGit(() => this.git(['ls-tree', '-r', '--name-only', '-z', tree, '--', literal]))
    if (!listed.split('\0').includes(file)) {
      await rm(join(this.requireRoot(), file), { recursive: true, force: true })
      return
    }
    await this.serialGit(() => this.git(['checkout', tree, '--', literal]))
  }

  private async restoreTargets(targets: readonly WorkspaceTarget[]): Promise<void> {
    for (const target of targets) await this.restoreFile(target.tree, target.file)
  }

  private async restoreRedo(redo: WorkspaceRedo): Promise<void> {
    for (const file of redo.files) await this.restoreFile(redo.tree, file)
  }

  private async loadState(): Promise<void> {
    if (this.gitDir === undefined || this.loaded) return
    this.loaded = true
    try {
      const parsed = JSON.parse(await readFile(join(this.gitDir, 'state.json'), 'utf8')) as Partial<PersistedState>
      if (parsed.version === STATE_VERSION) {
        this.state = {
          version: STATE_VERSION,
          patches: parsed.patches ?? {},
          redos: parsed.redos ?? {},
          ...(parsed.pending === undefined ? {} : { pending: parsed.pending }),
        }
      }
    } catch {
      // Missing or unreadable state: start from empty; snapshots still work.
    }
  }

  private persistState(): Promise<void> {
    return this.serialState(async () => {
      if (this.gitDir === undefined) return
      const path = join(this.gitDir, 'state.json')
      const temporary = `${path}.tmp`
      await writeFile(temporary, JSON.stringify(this.state), 'utf8')
      await rename(temporary, path)
    })
  }

  private serialGit<T>(operation: () => Promise<T>): Promise<T> {
    const result = this.gitTail.then(operation, operation)
    this.gitTail = result.then(() => undefined, () => undefined)
    return result
  }

  private serialState<T>(operation: () => Promise<T>): Promise<T> {
    const result = this.stateTail.then(operation, operation)
    this.stateTail = result.then(() => undefined, () => undefined)
    return result
  }

  private requireRoot(): string {
    if (this.root === undefined) throw new Error('workspace root is unavailable')
    return this.root
  }

  private async git(args: string[]): Promise<string> {
    const root = this.requireRoot()
    if (this.gitDir === undefined) throw new Error('snapshot git directory is unavailable')
    const { stdout } = await execFileAsync('git', [
      '-c', 'core.autocrlf=false',
      '-c', 'core.longpaths=true',
      '--git-dir', this.gitDir,
      '--work-tree', root,
      ...args,
    ], { cwd: root, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 })
    return stdout
  }

  private async sourceGit(args: string[]): Promise<string> {
    const { stdout } = await execFileAsync('git', ['-C', this.requireRoot(), ...args], {
      encoding: 'utf8',
      maxBuffer: 16 * 1024 * 1024,
    })
    return stdout
  }

  private splitPaths(output: string): string[] {
    return output.split('\0').filter(Boolean)
  }

  private pathBatches(paths: readonly string[]): string[][] {
    const batches: string[][] = []
    let batch: string[] = []
    let length = 0
    for (const path of paths) {
      if (batch.length > 0 && length + path.length > 24_000) {
        batches.push(batch)
        batch = []
        length = 0
      }
      batch.push(path)
      length += path.length + 16
    }
    if (batch.length > 0) batches.push(batch)
    return batches
  }
}

/** The user message that owns one tool call: latest `user/message` before it. */
export function userSeqForCall(events: readonly WorkspaceEvent[], callId: string): number | undefined {
  const callSeq = callSeqForCall(events, callId)
  if (callSeq === undefined) return undefined
  let found: number | undefined
  for (const event of events) {
    if (event.seq >= callSeq) break
    if (event.type !== 'user/message') continue
    const data = event.data as { source?: { kind?: string } } | undefined
    if (data?.source?.kind !== 'user') continue
    found = event.seq
  }
  return found
}

/** Sequence of one tool call event. */
export function callSeqForCall(events: readonly WorkspaceEvent[], callId: string): number | undefined {
  for (const event of events) {
    if (event.type !== 'tool/call') continue
    const data = event.data as { callId?: unknown } | undefined
    if (String(data?.callId) === callId) return event.seq
  }
  return undefined
}

/** Whether `child` is `parent` or sits underneath it. */
function isInside(child: string, parent: string): boolean {
  const rel = relative(parent, resolve(child))
  return rel === '' || (!rel.startsWith('..') && !isAbsolute(rel))
}

/** Whether a path is a filesystem root (e.g. `C:\`) — never snapshot those. */
function isDriveRoot(path: string): boolean {
  const parsed = resolve(path)
  return parsed === parsed.slice(0, 3) && /^[A-Za-z]:\\?$/.test(parsed)
}
