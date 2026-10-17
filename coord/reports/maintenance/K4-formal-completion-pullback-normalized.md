# K4 maintenance: FormalCompletionPullbackNormalized

The ten counted NOANSWER failures were provider HTTP 429 failures. Every run
from `Sheaf.AlgebraicGeometry.FormalCompletionPullbackNormalized.1792195909`
through `.1792196711` ended with `ERROR: exceeded retry limit, last status: 429
Too Many Requests` and wrote no `last.txt`. Five attempts failed before any work;
the others resumed reading or validating the already prepared proof. Similar
failures affected many unrelated items in the same dispatcher passes. The
dispatcher had a configured ceiling of 700 workers and hundreds of live sessions.
It discarded the fatal provider diagnostic when converting a missing final-answer
file to an empty `NOANSWER`, then relaunched a fresh session immediately.

An earlier, distinct compile failure followed upstream sync e47efb5a5. The helpers
`completionPullbackIso` and `powerQuotientIso` moved to
`WeilConjectures.AlgebraicGeometry.FormalSystemsPullback`; importing all of its
Sheaf re-export wrapper did not expose them. The worker had already repaired the
proof-only import and supplied a complete, reviewed proof. Maintenance did not
perform this item's mathematics or edit its Lean/module/DAG records.

The shared provider recovery was deployed concurrently by NK maintenance:
`/home/ubuntu/.local/bin/codex` points to
`/home/ubuntu/weil-launcher-all/codex_retry.py`. Its initial tested implementation,
documentation and regression suite are committed in the server's newtargets
repository as `a1a68055f2b73fe62674754cb95071667bd798ac`. It supervises dispatcher
worker invocations, retries temporary provider failures with jitter, resumes the
session where available, retains the original deadline and sandbox, and writes
a concrete BLOCKED diagnostic on exhaustion. Later concurrent maintenance has
added resume/admission handling; this K4 repair did not overwrite those changes.

Verification during K4 maintenance:

- The committed initial runner's 11 tests passed on the server.
- Ten applicable existing recovery regressions passed against the current locally
  installed runner; the original scope test was superseded by later explicit
  resume support. Direct assertions confirmed K4's exact output path is supervised
  and an unrelated /tmp output path passes through.
- The saved delivery `3cbddb91b3` landed normally on the live server at
  `c070278e531893762fc3a8ec1d372e681ae2d172`, landing
  `20261017T003424-L-3316109`, at 08:34:24 Asia/Shanghai. The lander closed the
  claim/return, and the dispatcher retired the pre-install worker.
- The landed item compiled cleanly in 2.8 seconds with
  `SHEAF_GROUP=MAINTK4Normalized SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh
  lean/Sheaf/AlgebraicGeometry/FormalCompletionPullbackNormalized.lean`.
- No Lean source changed and no global build was started by this maintenance.
  The normal global verifier remains responsible for the landing's final status.

The item-specific route note is
`tools/launcher/route-notes/Sheaf.AlgebraicGeometry.FormalCompletionPullbackNormalized.md`;
it is also installed in the launcher's route-notes directory for future prompts.
Historical counts were preserved. No process was killed. No claim, return,
dispatcher state or existing worker report was manually cleared by this maintenance.

Next worker: the theorem is already proved on main. If returned again, begin with
the current source and the retained sandbox, inspect the actual new diagnostic,
and use the normal dry-run/second-reader workflow. Retain the upstream helper
import and verify any interrupted delivery before repeating it. Provider recovery
cannot guarantee availability of an overloaded service; a further BLOCKED with
its preserved diagnostic identifies that condition without inventing a proof
failure or abandoning the item.
