# NN maintenance: bimodule word/path worker interruptions

The failures of `lem-coef-bimodule-word-path-approximation@new` were provider
HTTP 429 interruptions, not a Lean error or a mathematical defect. All eleven
completed run logs, from `1792196130` through `1792196923`, end with
`ERROR: exceeded retry limit, last status: 429 Too Many Requests`. None wrote
`last.txt`. The old dispatcher reduced this to an empty `NOANSWER:` and
started a new conversation. Several workers reached the initial reading and
searches, but no Lean module or node edit survived in the sandbox. The stage-1
delivery was already merged by Q54 at `80418f2647`; it was not a stage-2 return.

There was concurrent pipeline maintenance during this investigation. NK's
`a1a68055f2` added the installed `codex_retry.py` supervisor, with bounded
exponential jitter, exact-session recovery, and a provider diagnostic on
exhaustion. Other maintenance added dispatcher diagnostics/admission and
explicit session resumption. This repair retains those changes.

This investigation independently found an integration gap: the supervisor excluded
all `exec resume` calls, including the explicit UUID calls now emitted by the
dispatcher. Its retry argument builder also produced two `resume` tokens when
given such a call. A repeated 429 during dispatcher resumption would therefore
bypass recovery or form an invalid command. Concurrent Q65 maintenance committed
the same correction as `a5ae0952c3` before this session's final deployment.
The final comparison caught that overlap; this session preserved that committed
implementation and its tests, including Q126's `0fa398c792` saved-session fix.
Q57 subsequently committed the combined argument repair as `d901bdf2bd`.
Final integration testing caught an additional regression in that combined
version: `exec resume --last ... <uuid> -` was admitted despite its ambiguous
session selector. This session restores explicit rejection of `--last` and
`--all`, retains the final stdin-marker check, and redeploys the current
server source to the installed launcher atomically.
The repaired supervisor accepts
only explicit UUID resumes within its existing dispatcher output-path scope,
initializes the session from that UUID even if startup fails before the header,
and replaces the session argument without nesting `resume` commands.

This session's server changes under `/home/ubuntu/weil-newtargets`:

- `tools/launcher/codex_retry.py`: reject implicit session selectors even when
  a UUID is also present, preserving the dispatcher's exact-session boundary.
- `tools/launcher/test_codex_retry_resume.py`: four regressions for scope,
  arguments, and successful fake-CLI recovery after a second 429 before the header.
- `tools/launcher/codex-retry.md`: the additional regression command.
- `coord/reports/maintenance/NN-bimodule-word-path-provider.md`: this record.

`tools/launcher/test_codex_retry.py` has no final diff from the concurrent
committed repairs. The runtime installation was refreshed from the preserved
combined source with the selector correction, not from this session's draft.

Installed runtime path: `/home/ubuntu/weil-launcher-all/codex_retry.py`.
The existing `/home/ubuntu/.local/bin/codex` symlink already points there.
Existing files are backed up beside themselves with suffix
`.maint-NN-1792196947.bak`; newly created report/test files have final `.bak`
snapshots. The maintenance workspace also retains the original code and tests.

Validation: the current fourteen fake-CLI tests and four new resumed-worker
regressions pass. They start and stop only their own fake local children and
make no model requests. No Lean source, node statement, dependency record,
failure count, or active dispatcher state was changed. No Lean compile or
`lake build` was needed. No unrelated process was signalled or restarted.

Next worker: continue the normal stage-2 brief in the retained NN sandbox.
The run `1792196952` was still alive and reading the source during maintenance;
let it finish. The historical blank `NOANSWER` note does not identify a node
fault. The supervisor applies to future fresh and explicit-resume launches
without restarting the dispatcher. It does not retrofit an already loaded CLI
process. If the provider remains unavailable beyond the bounded recovery
budget, retain `codex-retry.json` and the request ID as infrastructure evidence;
failure counts remain counts and do not retire this item.

The provider guidance recommends bounded exponential backoff with jitter:
https://developers.openai.com/api/docs/guides/rate-limits . A 429 alone does
not establish the account's exact quota or limit; those were not inferred here.
