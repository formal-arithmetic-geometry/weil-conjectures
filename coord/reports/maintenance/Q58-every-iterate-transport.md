# Q58: provider failures for prop-every-iterate-trace

On 2026-10-17, maintenance inspected the dispatcher state, all seven attempt
directories, the retained sandbox, the launcher, and the server node, returns and
delivery/landing logs. Six terminated attempts end in a fatal provider HTTP 429;
none produced `last.txt`. The stored failure count is five because the old
dispatcher could drop an ended run between reap and work. These are transport
failures; they establish no mathematical rejection and no accepted split.

Run suffix and terminal request ID:

| Run | Request ID |
| --- | --- |
| 1792196337 | f09276b4-c8f3-4ab6-9fc5-6898f0098db5 |
| 1792196369 | 4c156da9-54e0-434e-999a-911d32e9edaa |
| 1792196408 | eeace7d2-cb49-493a-a5ff-3a328d82af0d |
| 1792196460 | b07cd30f-dc5a-4ab5-99b2-1e8e685912dd |
| 1792196564 | 97da5d33-0617-4af9-a1f6-af57047b3e29 |
| 1792196864 | 3ab2ae83-789e-4bba-a117-1f0ee96e1253 |

Logs are `/home/ubuntu/weil-launcher-all/run/Q58/prop-every-iterate-trace.<run>/log.txt`
on the launcher machine. Local maintenance evidence and verification are in
`/home/ubuntu/weil-launcher-all/maint/Q58-prop-every-iterate-trace-1792196892/`.

The common fix was installed during this maintenance investigation by NK
maintenance, in server commit `a1a68055f2b73fe62674754cb95071667bd798ac`:
`tools/launcher/codex_retry.py`, `test_codex_retry.py`, and `codex-retry.md`.
The local `~/.local/bin/codex` now points to
`~/weil-launcher-all/codex_retry.py`, so the already-running dispatcher uses the
supervisor on its next ordinary launch without a restart. Its original symlink
is retained as `~/.local/bin/codex.maint-NK-1792196275.bak`.

The supervisor retries terminal temporary 429s with bounded exponential jitter,
resumes saved sessions, preserves the sandbox and worker deadline, and writes a
specific provider `BLOCKED` diagnostic on exhaustion. Existing final answers win;
authentication and quota failures are not retried. This follows the retry
pattern in the [official OpenAI documentation](https://developers.openai.com/api/docs/guides/rate-limits).
The configured provider is an OpenAI-compatible gateway; this maintenance does
not infer its numerical account limit or guarantee its availability.

The initial wrapper's 11 tests passed, its installed hash matched the committed
server source, and the current server regression suite was also run explicitly
against the installed wrapper after subsequent shared maintenance updates:
11 tests passed. An initial rerun of the old test fixture failed only because it
expected explicit `exec resume` invocations to be excluded; shared follow-up
commit `a5ae0952c31d887797156fd16ea7208a894cae05` intentionally supervises those
invocations. The current fixture accepts that behavior. Q58 maintenance did not
overwrite the shared transport implementation or change admission settings.

The running item attempt `1792196895` (PID 2370935 at inspection) predates the
supervisor and continues making normal progress. It was not stopped. Its sandbox
is `/home/ubuntu/weil-newtargets-sandbox/Q58/prop-every-iterate-trace`.
The next worker/reader must resume and check that work against the stage-1 brief,
current blueprint and cited nodes, run the normal dry run, and complete the
independent reading/delivery. Earlier NOANSWER records require no statement
change. An exhausted provider error calls for checking gateway capacity and
`codex-retry.json`, while retaining the item and sandbox for another dispatch.

No node record, mathematical statement, proof, Lean file, claim, counter, return
entry or dispatcher state was edited by this Q58 maintenance. No build or Lean
compilation was needed, and no process was killed.
