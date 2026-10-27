Maintenance: B9 / WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic, stage 3

The repeated failures were caused by contradictory delivery checks, not by the item's
mathematics. `tools/stage3_delivery.py:check_lean` checked every line of the delivered
file against 100 characters, including unchanged upstream text. Line 14 of
`lean/WeilConjectures/SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean` is the
102-character public import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic`.
The worker's source-library contract required preserving that import verbatim.
Wrapping it was also ineffective: `tools/stage2_delivery.py:public_imports` only
recognizes horizontal whitespace between `import` and its module name, so it treated
the wrapped import as removed. Repeated dispatches therefore retried the same valid
proof against an unsatisfiable formatting requirement.

Evidence: dispatcher state recorded 25 tries for the `@new` key and the same blocker;
the retained sandbox's `delivery-current.log` reported exactly the line-14 diagnostic.
The earliest retained B9 run (1792760788), the following run (1792767324), and the last
completed run (1792784020) reported the same conflict. The earlier proof had been
landed by V2 on 2026-10-16, then lost in the 2026-10-20 upstream prefer-upstream sync;
the recovery assignment itself was legitimate, as documented in
`coord/preferred-upstream/WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic.md`.

The responsible protected tools had already been repaired immediately before this
maintenance run by server commit
`604df3075cc0a99420292708b248ddbf2cb40715` (2026-10-24 03:38:16 +08),
"stage-3 checks: enforce only compile, honesty and DAG consistency; other rules become
advisory notes". It changes `tools/stage3_delivery.py` and `tools/stage3_gate.py`.
The line-length diagnostic now becomes advisory; compilation, axiom, hollow-definition,
target-statement and DAG integrity checks remain enforced. This was an existing
maintainer change, not a tool edit made by this maintenance session. No further
launcher-owned or landing-tool change is needed for this failure.

Validation during this session:

- The shared checkout contains that fix. Running the existing `check_lean` and
  `enforced` functions on the retained packet produced one raw line-length diagnostic,
  zero enforced failures, and one advisory. Public imports match the current source
  exactly, no declaration statement changed, no forbidden construct was added, and
  textual sorry counts are 1 before / 0 after.
- The already-running B9 worker (run 1792784367) independently compiled the item
  remotely in 7.0 seconds, exit 0, without errors or warnings, then passed the actual
  remote delivery preflight and pushed
  `47b29763b6bc9571d29eeb3f0c35e31253c51d70`. The server delivery branch contains
  `604df3075cc` in its ancestry. This establishes that the real delivery path uses the
  repair. The worker is updating its previously stale report and may supersede that
  delivery commit with another report-only refresh of the same proof packet.

I changed no Lean source, DAG node, dispatcher state, claim, brief, admission setting,
review service or landing tool. I did not perform the item's mathematics, bypass a
check, start a lake build, stop another process, or add a limit or pause. I created
this report and a server maintenance record at
`/home/ubuntu/weil-conjectures-sheaf/coord/maintenance/B9-lower-star-acyclic-preflight-20261024.md`.
The server record is committed under `coord/.merge.lock` with `SHEAF_LEAD=L-only`
and the requested Bin Wu identity; the local maintenance REPORT.md records its commit.
Both new report files have `.bak` copies; no pre-existing file was overwritten.

The next worker should retain the existing proof and node packet and use the normal
delivery/review path. The 102-character import can stay unchanged. The old BLOCKED
note and any report paragraph saying this checker still refuses line 14 are stale
after `604df3075cc`. Do not re-prove the theorem, wrap or privatize that import, add
an exception to evade the checker, or reset the failure count. Delivery has already
succeeded; check the current `deliver/B9/WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`
branch and normal review records before submitting another packet. Independent
mathematical review and landing remain the normal pipeline's responsibility.
