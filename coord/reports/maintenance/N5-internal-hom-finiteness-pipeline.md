# N5 internal-Hom finiteness: pipeline maintenance

Item `lem-sfb-finite-field-internal-hom-finiteness`, stage 1, dispatcher key
`lem-sfb-finite-field-internal-hom-finiteness@new`, investigated 2026-10-17.

The repeated failures were model-service interruptions. Every one of the
eleven completed attempts from `1792193413` through `1792196979` ends with
`ERROR: exceeded retry limit, last status: 429 Too Many Requests`; none wrote
its final-answer file. The dispatcher only consumed that file, so its note
was the uninformative `NOANSWER:`. Unpaced relaunches of workers and maintenance
sessions across the pipeline amplified provider overload. Failure counts are
still counts; they must not disable the item.

The first attempt also hit a separate shared-ref race in stage-1 packaging.
Delivery preparation checked out one version of `origin/newtargets-dag`, but
preflight later resolved that mutable shared ref again, including for bundle
exclusion. Concurrent fetches could advance it. The resulting ancestry and
scope checks reported an outdated base and the unrelated generated
`coord/blueprint-index.tsv`. This was not evidence of a bad sandbox file.

Concurrent maintenance installed the shared repairs during this investigation:

- `a1a68055f2`: the `codex_retry.py` CLI supervisor preserves a known session,
  uses bounded delayed retries within the existing timeout and records an
  explicit exhausted-recovery diagnostic. Later commits `a5ae0952c3` and
  `0fa398c792` cover explicit resume and unavailable saved sessions.
- The installed `/home/ubuntu/.local/bin/codex` symlink points to that supervisor.
  Its `codex_admission.py` gate applies to new children immediately, counts
  legacy children and queues excess launches. On inspection it counted 436
  external children and queued new requests; no process was stopped.
- `783eefd226` captures the delivery's immutable checkout SHA and uses it
  consistently for bundle creation, server preflight and local fallback.
- `6fb280508f` and `0abb765411` preserve reader handoffs and interrupted reports.
  Dispatcher source changes apply on its next normal start. This task did not
  signal or restart the running dispatcher.

This maintenance adds the item-specific recovery brief at
`tools/launcher/route-notes/lem-sfb-finite-field-internal-hom-finiteness.md`,
installed locally under `/home/ubuntu/weil-launcher-nt/route-notes/`, together
with this report and `N5-internal-hom-finiteness-evidence.json`. It directs any
later author retry to validate the saved packet first and preserves the
independent reader's role. Shared tool fixes above belong to the concurrent
maintenance sessions; they are not claimed as changes authored here.

Verification exposed one additional supervisor regression: the server's
`resume_session` accepted `exec resume --last ... <UUID> -`, although `--last`
does not identify the dispatcher's explicit session. This task restores the
guard requiring stdin mode and rejecting `--last`, matching the installed
local supervisor. The existing invocation-scope regression covers the case.

Recovery was observed: worker `1792197005` passed no-push preflight at
`9e1f211c82` and `26b6faaf1b`, then wrote READY. The dispatcher started the
independent stage-1 reader `1792197756` (PID 3057570). The reader was alive at
the evidence snapshot. A dry run is not a delivered or reviewed result; the
normal independent review and delivery remain the reader's work.

No node statement, proof, dependency, Lean file, sandbox report, dispatcher
state or return was changed by this maintenance. No compilation or library
build was needed. Existing files replaced during installation have `.bak`
copies; newly created artifacts also have `.bak` snapshots. The final local
REPORT.md records validation, the maintenance commit and the latest status.
