/**
 * `src/workspace.ts` 的单元测试。
 *
 * 两层覆盖:
 *  1. 纯函数(`userSeqForCall` / `callSeqForCall`)——只依赖内存事件数组,任何机器都跑;
 *  2. 快照与回退主链路——在临时目录里建真实 git 仓库,让隐藏仓库真正拍快照、真正回写文件。
 *
 * 说明:git 相关用例全部挂在 `describe.skipIf(!gitAvailable)` 下,机器上没有 git 时
 * 自动跳过,纯函数用例照常执行。
 */

import { execFileSync } from 'node:child_process'
import { existsSync } from 'node:fs'
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'
import { WorkspaceSnapshots, callSeqForCall, userSeqForCall } from '../src/workspace.js'
import type { WorkspaceEvent } from '../src/workspace.js'

/** 本机是否有可用的 git;没有就跳过所有依赖真实仓库的用例。 */
const gitAvailable = ((): boolean => {
  try {
    execFileSync('git', ['--version'], { stdio: 'ignore' })
    return true
  } catch {
    return false
  }
})()

/** 本轮测试创建过的临时目录,统一在 afterEach 里清理。 */
const tempDirs: string[] = []

afterEach(async () => {
  while (tempDirs.length > 0) {
    const dir = tempDirs.pop()
    if (dir === undefined) continue
    // Windows 上 git 偶尔还握着句柄,重试几次即可;清理失败不影响用例结论。
    await rm(dir, { recursive: true, force: true, maxRetries: 5, retryDelay: 50 }).catch(() => {})
  }
})

/** 建一个临时目录并登记待清理。 */
async function makeTempDir(prefix: string): Promise<string> {
  const dir = await mkdtemp(join(tmpdir(), prefix))
  tempDirs.push(dir)
  return dir
}

/** 在指定仓库目录里同步执行一条 git 命令。 */
function git(cwd: string, ...args: string[]): string {
  return execFileSync('git', ['-C', cwd, ...args], { encoding: 'utf8' })
}

/**
 * 建一个带初始提交的工作区:`keep.txt` 为 v1,`.gitignore` 排除 `ignored.txt`。
 *
 * 刻意关掉 `core.autocrlf` 与 `commit.gpgsign`,避免 Windows 换行转换和签名环境干扰断言。
 */
async function createWorkspace(): Promise<string> {
  const root = await makeTempDir('dsh-ws-src-')
  git(root, 'init', '--quiet')
  git(root, 'config', 'user.email', 'dsh-test@example.com')
  git(root, 'config', 'user.name', 'dsh-test')
  git(root, 'config', 'core.autocrlf', 'false')
  git(root, 'config', 'commit.gpgsign', 'false')
  await writeFile(join(root, 'keep.txt'), 'v1\n', 'utf8')
  await writeFile(join(root, '.gitignore'), 'ignored.txt\n', 'utf8')
  git(root, 'add', '--', '.gitignore', 'keep.txt')
  git(root, 'commit', '--quiet', '-m', 'init')
  return root
}

/** 收集告警的假 logger:快照失败时源码只写日志,不抛错,所以断言要看这里。 */
function createLogger(): { warnings: string[]; logger: { warn(message: string, cause?: unknown): void } } {
  const warnings: string[] = []
  return {
    warnings,
    logger: {
      warn(message: string, cause?: unknown): void {
        warnings.push(cause === undefined ? message : `${message} ${String(cause)}`)
      },
    },
  }
}

type AroundExec = Parameters<WorkspaceSnapshots['around']>[0]
type AroundNext = Parameters<WorkspaceSnapshots['around']>[1]
type AroundResult = Awaited<ReturnType<AroundNext>>

/** 构造一次 root 工具调用(`parent` 必须缺省,否则源码直接跳过拍快照)。 */
function toolExec(callId: string): AroundExec {
  return {
    rootCallId: callId,
    callId,
    name: 'write_file',
    arguments: {},
    signal: new AbortController().signal,
  } as unknown as AroundExec
}

/** 工具调用成功返回的最小结果形状。 */
const OK_RESULT = { isError: false, value: null, content: [] } as unknown as AroundResult

/** 真实用户消息的 seq,与 {@link callEvents} 保持一致。 */
const USER_SEQ = 2

/** 构造最小事件流:developer 消息 → 真实 user 消息 → 一次 tool/call。 */
function callEvents(callId: string): WorkspaceEvent[] {
  return [
    { seq: 1, type: 'developer/message', data: { source: { kind: 'developer' } } },
    { seq: 2, type: 'user/message', data: { source: { kind: 'user' } } },
    { seq: 3, type: 'tool/call', data: { callId } },
  ]
}

/** 读取文本并去掉行尾换行,避免 CRLF 差异干扰断言。 */
async function readTrimmed(path: string): Promise<string> {
  return (await readFile(path, 'utf8')).trim()
}

describe('userSeqForCall / callSeqForCall', () => {
  // 中间夹一条 source.kind 不是 user 的 user/message,以及一条 call 之后的真实用户消息,
  // 用来验证"取 call 之前最近一条真实用户消息"这一语义。
  const events: WorkspaceEvent[] = [
    { seq: 1, type: 'developer/message', data: { source: { kind: 'developer' } } },
    { seq: 2, type: 'user/message', data: { source: { kind: 'user' } } },
    { seq: 3, type: 'user/message', data: { source: { kind: 'tool' } } },
    { seq: 4, type: 'assistant/message', data: {} },
    { seq: 5, type: 'tool/call', data: { callId: 'call-a' } },
    { seq: 6, type: 'user/message', data: { source: { kind: 'user' } } },
    { seq: 7, type: 'tool/call', data: { callId: 'call-b' } },
    { seq: 8, type: 'tool/call', data: { callId: 99 } },
  ]

  it('返回 tool/call 之前最近一条真实用户消息的 seq', () => {
    // seq 3 的 source.kind 是 tool,必须跳过,因此 call-a 归属 seq 2。
    expect(userSeqForCall(events, 'call-a')).toBe(2)
    // call-b 之前还有 seq 6 这条真实用户消息,应该覆盖更早的 seq 2。
    expect(userSeqForCall(events, 'call-b')).toBe(6)
  })

  it('忽略 tool/call 之后的用户消息,并且没有匹配 call 时返回 undefined', () => {
    expect(userSeqForCall(events, 'call-a')).not.toBe(6)
    expect(userSeqForCall(events, 'missing-call')).toBeUndefined()
  })

  it('callSeqForCall 返回该 tool/call 的 seq,并把数字 callId 归一成字符串比较', () => {
    expect(callSeqForCall(events, 'call-a')).toBe(5)
    expect(callSeqForCall(events, 'call-b')).toBe(7)
    expect(callSeqForCall(events, 'missing-call')).toBeUndefined()
    // 源码用 String(data.callId) 比较,数字 99 应能用 '99' 命中。
    expect(callSeqForCall(events, '99')).toBe(8)
  })

  it('事件流里没有真实用户消息时返回 undefined', () => {
    const noUser: WorkspaceEvent[] = [
      { seq: 1, type: 'developer/message', data: { source: { kind: 'developer' } } },
      { seq: 2, type: 'tool/call', data: { callId: 'call-x' } },
    ]
    expect(userSeqForCall(noUser, 'call-x')).toBeUndefined()
  })
})

describe.skipIf(!gitAvailable)('WorkspaceSnapshots · 快照与回退', () => {
  it('around 记录改动后 restore 回到最早 pre-image,commit 后的 redo 复原当前内容', async () => {
    const root = await createWorkspace()
    // 快照仓库必须放在工作区之外,否则源码会以"会把自己的对象拍进快照"为由拒绝。
    const storeRoot = await makeTempDir('dsh-ws-store-')
    const sink = createLogger()
    const snapshots = new WorkspaceSnapshots({
      sessionId: 'session-main',
      cwd: root,
      storeRoot,
      logger: sink.logger,
    })
    const events = callEvents('call-1')

    const out = await snapshots.around(toolExec('call-1'), async () => {
      await writeFile(join(root, 'keep.txt'), 'v2\n', 'utf8')
      await writeFile(join(root, 'new.txt'), 'created\n', 'utf8')
      await writeFile(join(root, 'ignored.txt'), 'ignored\n', 'utf8')
      return OK_RESULT
    }, () => events)

    // 拍快照失败只会写日志;这里顺带确认整条链路没有静默降级。
    expect(out).toBe(OK_RESULT)
    expect(sink.warnings).toEqual([])

    // 工具调用之后人工再改一次,这一步不在任何 around 里,不属于被记录的 patch。
    await writeFile(join(root, 'keep.txt'), 'v3\n', 'utf8')

    const restored = await snapshots.restore([USER_SEQ], 'op-1')
    expect(restored.warning).toBeUndefined()
    // keep.txt 改回内容 + new.txt 删掉 = 2 个文件;ignored.txt 不在快照范围内。
    expect(restored.files).toBe(2)
    expect(await readTrimmed(join(root, 'keep.txt'))).toBe('v1')
    expect(existsSync(join(root, 'new.txt'))).toBe(false)
    expect(existsSync(join(root, 'ignored.txt'))).toBe(true)

    await snapshots.commit('op-1')
    const redone = await snapshots.redo('op-1')
    expect(redone.files).toBe(2)
    expect(await readTrimmed(join(root, 'keep.txt'))).toBe('v3')
    expect(await readTrimmed(join(root, 'new.txt'))).toBe('created')
  }, 60_000)

  it('rollback 把文件恢复到 restore 之前的现场', async () => {
    const root = await createWorkspace()
    const storeRoot = await makeTempDir('dsh-ws-store-')
    const sink = createLogger()
    const snapshots = new WorkspaceSnapshots({
      sessionId: 'session-rollback',
      cwd: root,
      storeRoot,
      logger: sink.logger,
    })
    const events = callEvents('call-1')

    await snapshots.around(toolExec('call-1'), async () => {
      await writeFile(join(root, 'keep.txt'), 'v2\n', 'utf8')
      await writeFile(join(root, 'new.txt'), 'created\n', 'utf8')
      return OK_RESULT
    }, () => events)

    // restore 之前的现场:keep.txt 停在 v3,new.txt 已存在。
    await writeFile(join(root, 'keep.txt'), 'v3\n', 'utf8')

    const restored = await snapshots.restore([USER_SEQ], 'op-2')
    expect(restored.files).toBe(2)
    expect(await readTrimmed(join(root, 'keep.txt'))).toBe('v1')

    await snapshots.rollback('op-2')
    expect(await readTrimmed(join(root, 'keep.txt'))).toBe('v3')
    expect(await readTrimmed(join(root, 'new.txt'))).toBe('created')
  }, 60_000)
})

describe('WorkspaceSnapshots · 降级路径', () => {
  it('cwd 缺失时 restore 返回 0 个文件与告警,around 仍原样返回工具结果', async () => {
    const storeRoot = await makeTempDir('dsh-ws-store-')
    const sink = createLogger()
    const snapshots = new WorkspaceSnapshots({
      sessionId: 'session-no-cwd',
      cwd: undefined,
      storeRoot,
      logger: sink.logger,
    })

    const restored = await snapshots.restore([1], 'x')
    expect(restored.files).toBe(0)
    expect(restored.warning ?? '').toContain('没有工作目录')

    // 快照不可用时 around 必须透明放行,不能把工具调用搞失败。
    const out = await snapshots.around(toolExec('call-9'), async () => OK_RESULT, () => callEvents('call-9'))
    expect(out).toEqual(OK_RESULT)
  })

  it.skipIf(!gitAvailable)('快照目录位于工作区内时拒绝拍快照并降级', async () => {
    const root = await createWorkspace()
    // 故意把快照仓库放进工作区:源码要求它必须在仓库之外。
    const storeRoot = join(root, '.snapshot-store')
    await mkdir(storeRoot, { recursive: true })
    const sink = createLogger()
    const snapshots = new WorkspaceSnapshots({
      sessionId: 'session-inside',
      cwd: root,
      storeRoot,
      logger: sink.logger,
    })

    const restored = await snapshots.restore([1], 'x')
    expect(restored.files).toBe(0)
    expect(restored.warning ?? '').toContain('快照目录')
  }, 30_000)
})
