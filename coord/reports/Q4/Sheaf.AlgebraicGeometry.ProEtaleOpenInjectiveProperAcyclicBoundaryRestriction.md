## What changed

Completed the Lean proof of
`AlgebraicGeometry.Scheme.isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper`
without changing its signature, public imports, coefficients, or arbitrary-injective scope.
The proof applies a fully proved closed-restriction detection theorem, identifies evaluated
higher direct images with the published object hypercohomology by a K-injective resolution,
and invokes one remaining local hypercohomology statement.

Added `Sheaf.AlgebraicGeometry.ProEtaleClosedRestrictionTestDetection`, with a complete proof of
`AlgebraicGeometry.Scheme.isZero_closedRestriction_of_boundary_tests`.
This is independent of proper morphisms, finite coefficients, derived categories and
injectivity. Its proof uses the existing `localization_cover` construction from
`ProEtaleRingedLocalizationSequence` through a private proof import, rather than reconstructing
the affine geometry. It proves the closed direct image of inverse image zero by sectionwise
sheaf separation: open pieces have empty closed pullback; boundary pieces have an invertible
specialization unit and zero source. The closed counit and scalar transport give the specified
constant-ring pullback vanishing.

Added `Sheaf.AlgebraicGeometry.ProEtaleProperOpenBoundaryTestHypercohomology` for the remaining
local proper/open section-group calculation. This isolates Step 2 of the assigned node after
the affine localization and before descent. It concerns one affine weakly contractible,
boundary-specializing test and one ordinary hypercohomology group, with neither a higher
direct image nor a closed inverse image in the conclusion. The original item has no holes.
Its assembly proof includes the resolution, exact-evaluation and single-complex comparisons;
it is not just an application of a renamed copy of its statement.

All added imports in the item are private proof imports. No other existing module or existing
node was changed, and no definition or target statement was changed. No change record is
needed. The two new public declarations have new nodes in the same chapter and unit.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper`.
Also proved the new generic theorem
`AlgebraicGeometry.Scheme.isZero_closedRestriction_of_boundary_tests`, and the private
K-injective comparison helper `evaluation_higherDirectImage` in the item.

Added one hole, and this is the only `sorry` in the delivered Lean files:
`AlgebraicGeometry.Scheme.isZero_properOpen_boundary_test_hypercohomology`, node
`lem-sp-proetale-proper-open-boundary-test-hypercohomology`.
The remaining calculation still concerns arbitrary injective pro-etale coefficients, without
an etale-origin witness. The original item is reduced to this local calculation with its
localization, evaluation and descent glue proved. Holes closed: 1. Holes added: 1.
This is a decomposition with net zero holes, not a net proof closure.

Edge cases checked against the statements and constructions: the zero coefficient ring,
empty source open, identity base open (then a boundary-specializing test must be empty), and
empty closed complement. The detector uses the actual empty-site sheaf axiom. In the local
statement positive degree remains explicit; no degree-zero or nonclassical etale-origin
assumption was silently substituted.

Single-file server compiles established the new local interface, the complete generic
detector, and the complete item proof. The final sandbox compile and delivery preflight check
the files together in dependency order, including the axiom and hole checks.

## No longer needed

No modules are withdrawn and no global dependency is claimed pruned. No original public
import was removed. The original bounded w-contractible extension and closed-localization
inputs remain needed inside the proved detector's localization-cover construction. The
extension-by-zero base-change and restriction-of-injectives inputs remain in the local
cohomology plan. They are no longer direct assembly dependencies of the item; its node now
records the exact assembly route through the two new statements and the evaluation APIs.

The etale-origin-only modules `ProEtaleProperBoundaryCohomology` and
`ProEtaleProperBoundaryCohomologyOfClosedRestriction` are not imported: their extra hypothesis
is unavailable here. `ExceptionalBaseChangeCartesianOpenInjectiveAcyclic` is also not imported:
its finite-stage model's recorded proof already uses the parent open-injective acyclicity
obligation, so that apparent shortcut would be mathematically circular. These modules are
not claimed globally unused, and no adopted source-library declaration was removed.

## Where the brief, the DAG or earlier work was wrong

The recorded dependencies implement the affine geometry, restriction and evaluation, but do
not supply the arbitrary-injective local cohomology calculation. The narrower existing
proper-boundary theorem requires an explicit etale-origin witness for J. No such witness is
part of this item, and injectivity alone is not a justification for inserting one. The new
local theorem keeps this gap visible. Degree-zero specialization vanishing and exact
evaluation alone are not asserted to prove its positive-degree cohomology vanishing.

The item's existing `created.item` is a module name, so `blueprint_refs.py ancestor` on the
item reports a null ancestor. Following its actual node ancestry reaches
`lem-sp-proetale-open-injective-proper-acyclic`, whose recorded blueprint ancestor is
`cor-exc-base-change-open-immersion-general`. The two new nodes record that ancestor and the
full intervening node chain. No existing blueprint field or unit route was altered.

Mathlib semantic, natural-language and source searches found general injective-resolution,
section restriction and sheaf-separation results, but no matching proper/open local theorem.
The searches are recorded on both new nodes. The existing project's localization-cover and
specialization-unit proofs do close the generic detector, so it has no deferred geometric
lemma.

## New nodes

`lem-sp-proetale-closed-restriction-test-detection` records the general closed-restriction
criterion and its complete Lean proof in
`lean/Sheaf/AlgebraicGeometry/ProEtaleClosedRestrictionTestDetection.lean`.

`lem-sp-proetale-proper-open-boundary-test-hypercohomology` records the remaining strictly
local section-group calculation in
`lean/Sheaf/AlgebraicGeometry/ProEtaleProperOpenBoundaryTestHypercohomology.lean`, with the
inherited source step, proof plan and its precise arbitrary-injective scope. No change
records were added because only the item, its own node and new modules/nodes are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleClosedRestrictionTestDetection": "d099de30b1c1b58317af8de9f07ad632554a3593", "Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicBoundaryRestriction": "37ca8e113e093267ad8081d73ae1a93c99b19148", "Sheaf.AlgebraicGeometry.ProEtaleProperOpenBoundaryTestHypercohomology": "d67e2296ecdd8e3fd6fb4db80c37f650df21d0bc"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness": {"hash": "9e5fade8bfe1860f830030c1bef852c5fb56dfed", "status": "OK"}}, "seconds": 80, "time": "2026-10-28T12:12:34+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
