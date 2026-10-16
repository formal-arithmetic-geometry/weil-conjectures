# Q25 finite-coefficient adjoint comparisons maintenance

The repeated failure was stale maintainer-owned metadata. deliver.py preserves
the existing node's source from origin/newtargets-dag. The old source.place
cited SGA4, so review_split.py rejected every corrected sandbox under the
2026-10-16 route lock.

Changed only source in
dag/nodes/sec-smooth-purity/lem-pur-finite-coefficient-adjoint-comparisons.json
on the authoritative live DAG and then the side project. The replacement is
the existing sandbox proposal, with the current main-20261015 smooth comparison
source and an explicit description of the agent-written extension to arbitrary
separated finite-type morphisms. The source file exists in both repositories.

Live commits: f14d2696058e060b4e839cc4b18df357e94dc928 and
562146ceb7ad47221fa005a476352f09a99d9f45. The second corrects an accidental
JSON serialization/indentation defect in the initial write; their combined
diff changes only the two source strings.
Side refresh: 40f6cb3edcaa7013815c3460c060e27538a573aa.
Every edit and commit used the corresponding coord/.merge.lock and the
requested Bin Wu identity. Both original node files are saved beside them
with suffix .maint-Q25-1792173031.bak.

Validation: both committed node files parse, match their backups outside
source, and have equal sources. All 65 retained citation records pass;
the 40 proof dependencies equal the union of the 13 proof steps, and the
statement is unchanged. The running Q25 worker's required normal delivery
dry run completed successfully:

    OK (not pushed) deliver/Q25/lem-pur-finite-coefficient-adjoint-comparisons at 8df04f7675: preflight passed

The retained sandbox is ready for the normal independent second reading.
Keep its algebra pruning and current blueprint chart argument; do not restore
lem-coef-finite-free-extension or lem-pur-torsion-top-trace. The two
declared off-unit smooth comparison edges are advisories. No Lean,
mathematics, delivery tools, route checks, claims, or failure counters were
changed by this maintenance. No compilation or lake build was run.

The full local maintenance report and evidence are in
/home/ubuntu/weil-launcher-all/maint/Q25-lem-pur-finite-coefficient-adjoint-comparisons-1792173031/REPORT.md
on the launcher machine.
