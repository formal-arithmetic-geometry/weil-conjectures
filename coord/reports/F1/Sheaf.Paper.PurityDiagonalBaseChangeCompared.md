## What changed

Proved `WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange` in
`Sheaf.Paper.PurityDiagonalBaseChangeCompared`. The self-product square and its flip
supply the Cartesian assertion; Mathlib supplies smoothness of both projections.
The existing `Dnc.invertibleExponent P aX` supplies the coefficient condition.
The library's `Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`
applies to both squares; `Etale.isIso_dualizingComplexBaseChangeMap_iff` identifies
its coefficient-unit component with each specified dualizing mate.

All signatures, public imports and definitions are unchanged. In particular the three
explicit diagonal restriction/comparison definitions retain the inverse of the specified
mate, the canonical pullback composition, identity pullback and comparison-site transport.
The proof preserves the unit's diagonal/base-change route and uses no purity orientation.
Only the coefficient lemma in `PurityDncComparisons` is used, not DNC geometry or purity.
Updated the node's proof, proof dependencies and origin to record this route.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange`
(node `lem-pur-diagonal-base-change`).

There are zero `sorry`s left in the item module. Added zero holes and zero split theorems.
The imported coefficient lemma `WeilConjectures.PurityFiniteSetting.Dnc.invertibleExponent`
is an existing named theorem with `sorry` (node `lem-pur-dnc-section-geometry`);
this delivery uses its statement and does not claim to close its hole.
The upstream smooth-base-change theorem also has its existing proof dependencies;
closing this item's hole does not assert that its transitive axiom closure is finished.

## No longer needed

Removed these eight proof-only imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity`
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.PurityFiniteSetting`
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`

Added the proof-only import `Sheaf.Paper.PurityDncComparisons` for its existing coefficient
exponent lemma and the published smooth-base-change API it publicly imports.

The proof no longer separately uses nodes `def-weil-proper-morphism`,
`lem-pod-separated-finite-type-base-change`, `def-weil-exceptional-inverse-image`,
`def-weil-finite-type-morphism`, or `thm-pur-cohomological-smoothness`: the recorded
interfaces and existing Mathlib pullback instances suffice, and the library's smooth
ambient base-change theorem already states exactly the needed canonical mate invertibility.

The explicit comparison definitions already use the etale finite-coordinate composition
and identity comparison. The proof therefore needs no separate applications of
`lem-pur-proetale-constant-ring-composition`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`def-weil-derived-pullback-tensor-hom`, or
`lem-pur-proetale-derived-pullback-identity`. Removed the obsolete top-level tool approvals
for `lem-weil-pbc-proetale-derived-pullback-composition` and the already stale
`lem-weil-proetale-isomorphism-inverse-image`; retained the smooth-dimension approval.

These are removals of direct proof dependencies of this item. Several modules remain
transitively imported for other declarations; no global module-pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement, changed signature, definition repair or forced consumer adaptation
was needed. The old seven-step DAG plan used general pro-etale module composition and
identity nodes although the existing definitions already construct the specified chain
in finite etale coordinates and transport it to the actual pro-etale section invariant.
The existing smooth ambient base-change theorem is a shorter route than extracting the
comparison from the larger cohomological-smoothness theorem. No new node is needed.

The saved Mathlib searches found smooth-dimension base-change stability, but no complete
exceptional-dualizing comparison theorem in Mathlib. Library search found the theorem
used above. The compile-only import-direction check permits the new import.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
