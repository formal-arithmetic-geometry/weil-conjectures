# NY stage-1 delivery admission repair

The earlier missing target/source failure was repaired by 76b4fd0fe4 and
2fec47bc8c. The second reader then waited 1,237 seconds in deliver.py.
At diagnosis, deliver.py NY det-pe-hypercover-complex (pid 4107061) held
deliver-NY.lock after 20 minutes while using server preflight slot 4;
other NY deliveries waited for this group-wide lock. Each delivery already
has an isolated worktree, so serializing unrelated items was unnecessary.
The shared preflight log also records 700-950 s admission waits. The old
poll-and-race allocator allowed newer arrivals to overtake older requests.
The overloaded server separately waited up to 180 s before each preflight.

Stage 1 now locks by group/item and packages detached, so it does not mutate
a shared local branch while another legacy dry run is active. The preflight
allocator now admits live tickets in registration order, reaps dead ticket
owners using flock, and prints wait progress. Slot capacity and all preflight
checks are unchanged. The brief's trailing dot is accepted. The existing
lock validator is updated for the narrower stage-1 key.

Four real-process/AST regressions passed on the launcher before deployment;
the same suite runs on the server before this commit. Installed originals
and changed server files have .maint-NY-admission-1792178150.bak backups.
New requests load the repair. Existing callers are left to finish normally.
No process belonging to another worker was killed, no dispatcher count was
changed, and no mathematical record or Lean file was edited or compiled.

The sandbox already contains a second-reading audit and a statement dispute
about ell-invertibility. This maintenance repair does not decide that dispute;
the normal mathematical reviewer must assess it. See the launcher's final
REPORT.md for the full dry-run result and commit identifier.


Follow-up capacity repair: all 120 worktree slots were occupied during the
end-to-end replay. Their polling allocator had the same overtaking problem.
It now uses the same ordered ticket allocator, without holding a delivery
lock while waiting for capacity or retaining a slot while waiting for a
delivery lock. Both capacities retain their deployed defaults. The suite
now contains five passing tests, including worktree FIFO admission. The
first admission repair is commit 9fdb8a0bbf0aa331ff059c484e88c1c70a14a5f7.


The replay progressed through worktree admission, then found more than 100
waiters on the shared fetch mutex. The installed coalescing code checked its
completed-fetch stamp only after taking that mutex, so covered requests still
waited. Shared fetch now checks the stamp before acquisition and while waiting,
and publishes successful start timestamps atomically. Uncovered requests print
their elapsed wait. Explicit refspecs retain individual fetches. The regression
suite now has six passing tests, including completion under a held fetch mutex.
The replay subsequently reached server preflight with zero preflight queue wait.


Final operational validation (2026-10-17 03:33 launcher time):

`python3 -u /home/ubuntu/weil-launcher-nt/deliver.py NY nt-target-poincare-tate-bc --no-push .`
completed with exit code 0 and:

`OK (not pushed) deliver/NY/nt-target-poincare-tate-bc at 4f00e52280: preflight passed`

The replay used item-specific isolation, detached packaging and the ordered
worktree/server-preflight allocators. Its server admission wait was 0 s.
The final fetch-wait improvement was additionally verified by the sixth
regression on both machines. The legacy group/full-pool resource checks
also passed. All installed sources match the reviewed candidate bytes.
No mathematical delivery was pushed by maintenance.

Implementation commits: 9fdb8a0bbf0aa331ff059c484e88c1c70a14a5f7,
2388dd40ea98f966705c3d3fb12a73bab4bfaf50,
d4e6ba1a998f4cd666be7db1f3eea00d6f3a3df6,
144458d56349464561d289c91d386c8577e7823f.
Backups include .maint-NY-fetch-1792178150.bak and this record's
.maint-NY-verified-1792178150.bak in addition to the earlier backups.
The full report and execution logs are in
/home/ubuntu/weil-launcher-all/maint/NY-nt-target-poincare-tate-bc-1792178150/.
