The repeated failure is a bug in the protected landing checker
`/home/ubuntu/weil-conjectures-sheaf/tools/stage3_delivery.py:559`, function
`edge_fails`, introduced by server commit `c10a0ed635e`. The production fix remains
unapplied: the task explicitly prohibits editing “the landing tools” and directs
that their needed changes be described here. This checker is shared by
`preflight_delivery.py`, `merge_delivery.py` and `batch_land.py`; changing only a
worker-side copy would not repair landing.

The gate says inherited baseline cycles must not block a delivery, but its test at
line 592 requires mutual baseline reachability between the item and every added
dependency. Here that dependency is the new split helper
`lem-coef-system-total-enriched-transpose`, which cannot be reachable on a
baseline where it does not exist. This rejects a factorization of dependencies
already cyclic on that baseline.

Evidence:

- All six supplied worker logs contain the same `proof_deps gains
  lem-coef-system-total-enriched-transpose` diagnostic. `attempts.json` records
  the exact runs and messages; the second run tried both citation versions.
- The dispatcher continued dispatching while maintenance ran. Its initial state
  had `tries=1`, `blocked=5`; the later `dispatcher-state.json` has `tries=2` and
  an active worker. No retry counts, claims, dispatch settings or limits changed.
- A read-only replay of the actual packet against committed server baseline
  `d994cfa36f52a104b6f646c895140a7b26c30a1c` reproduces exactly one refusal.
  This uses all 36,297 nodes from DAG tree
  `83086885810b5221e131b3662d436f55b0764a80`, not a graph guessed from the log.
- The item reaches each of `def-sf-finite-adjunction-diagram-data` and
  `def-coef-finite-adjunction-system-data` in two baseline edges; they reach the
  item in 36 and 43 edges respectively. These are the helper's only dependencies
  with return paths. Complete paths are in `reproduction.json`.
- The checker snapshot matches committed and live server source SHA-256
  `aee291446b1b57f9000f2ab737ed39a346655a8c525c9999623fe0e94a4ca7c5`.
- The earlier A4 delivery was landed at `d8f315a3923` / landing
  `20261025T201250-L-2377945`, closing one of two holes. The current X5 packet
  addresses the remaining hole. There is no X5 push to land from these failures.
  Server delivery records and `~/cc1/autoland.log` corroborate the A4 landing.

The required repair is in `edge_fails`, not the theorem statement or proof plan.
Recognize a newly introduced helper by walking through new helper nodes to their
first baseline dependencies. Every such dependency that returns to the parent
must already be mutually reachable with that parent in the baseline. Keep
rejecting missing nodes, self edges, genuinely new cycles, new helper cycles and
new connections between previously separate baseline components. A helper that
directly depends on its own parent must not receive the inherited-cycle exception.

`proposed-stage3-cycle-factoring.patch` is a concrete, unapplied patch for that
repair. `proposed-cycle-gate.py` contains its helper. The read-only harness
`verify-cycle-gate.py` loads the original checker function from
`stage3_delivery.py.bak` and tests the proposed change in memory. All 14 tests
pass (`validation.log`), including the actual 36,297-node packet replay and
negative controls for the cycle cases above. This validates the graph gate only;
it is not a full preflight, a proof review, or a claim that the delivery passed.
No Lean files changed, so no Lean compile or `lake build` was run by maintenance.

Files created locally are this report, the proposed patch/helper, regression
harness, source backup and supporting JSON/log/checksum files. Durable copies
are committed on the server under
`coord/reports/maintenance/X5-descended-counit-cycle-1792964598/` using
`SHEAF_LEAD=L-only flock coord/.merge.lock` and author Bin Wu
`844524296@qq.com`. The commit hash is recorded in the local
`server-commit.txt` and the final response. This is an evidence and proposed-fix
commit only. Existing production tools, DAG nodes, modules, briefs, worker
sandbox files and dispatcher files were not edited. `.bak` copies preserve the
checker source and any maintenance artifact overwritten during preparation.

For the next worker: the complete proof packet remains in
`/home/ubuntu/weil-sandbox/X5/Sheaf.SixFunctors.IntegralExceptionalDescendedCounit`.
It closes the original remaining hole and introduces one documented system-level
transpose hole in `Sheaf.SixFunctors.SystemTotalEnrichedTranspose`. Required
definition citations must stay accurate; deleting them to evade this gate would
hide dependencies. The landing-tool owner must install the checker repair under
the merge lock. After it reaches the fetched server baseline, run normal
`deliver3.py X5 Sheaf.SixFunctors.IntegralExceptionalDescendedCounit --no-push`,
then normal delivery and independent review. The present live gate will continue
rejecting this unchanged packet until repaired; maintenance introduced no pause,
throttle, admission limit or concurrency cap.

To reproduce the isolated checks from either evidence directory, run
`python3 verify-cycle-gate.py`. The compressed graph is a committed baseline
snapshot; it is not a replacement for live project records. The proposed patch
has not been applied to any production or worker tool.
