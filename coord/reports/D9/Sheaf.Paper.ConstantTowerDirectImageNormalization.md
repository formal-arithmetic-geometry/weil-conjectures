## What changed

Completed the three remaining proofs in `Sheaf.Paper.ConstantTowerDirectImageNormalization`.
The ordinary comparison is assembled from scalar-extension and inverse-image adjunctions,
with the required formula on arbitrary pure tensor sections, strict transition compatibility,
and uniqueness. The derived comparison descends the invertible counit comparison from a
resolving class of flat K-flat models; its normalization holds on all homotopy objects.
The four final normalizations follow from derived-unit factorization, the evaluated mate,
the conjugate-adjunction unit identity, and naturality of mates for the augmentation square.

The model's four fields are now parameterized over abstract categories and specialized by
`ReductionModel`. This preserves their mathematical content and prevents repeated expansion
of chosen concrete sheaves during kernel checking. The definition change is recorded in
`coord/changes/constant-normalization-reduction-model-data.md`. There are no source-library
edits, new axioms, new holes, forced consumer adaptations, or withdrawn modules.
The existing node records the actual proof route and the added generic model record.

## Proved and sorry left

Closed all three original holes (not a decomposition):

- `AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.ordinaryReductionPull_existsUnique`
- `AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.reductionPull_existsUnique`
- `AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.constantTowerDirectImageNormalization`

Their node is `lem-sf-cbc-constant-tower-direct-image-normalization`.
Holes added: zero. Sorries left in the delivered module: zero. No statements were split off.
Existing imported dependencies are used as stated; this report counts the item's direct
holes rather than claiming that every dependency has a sorry-free axiom closure.

## No longer needed

Removed imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The following planned direct proof dependencies are replaced by the categorical
factorization and mate arguments:

- `def-weil-pbc-proetale-operations`
- `lem-pe-constant-left-module-inverse-image`
- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-ringed-tower-pushforward-limit-comparison`
- `lem-weil-tower-category-levelwise-abelian`
- `prop-pur-kinjective-resolutions-exist`

Removed obsolete top-level tool approvals, preserving the order of the remainder:

- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-ringed-tower-pushforward-limit-comparison`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-pe-constant-left-module-inverse-image`

These are removals from this proof's planned direct route. Some remain in the statement
dependencies or are used transitively by retained infrastructure. No declaration, source
module, or DAG node is withdrawn, and no globally unreachable module is claimed here.
The blueprint unit and all four of its conclusions remain intact.

## Where the brief, the DAG or earlier work was wrong

The planned diagram-site and generic projection-mate detour is unnecessary for this
normalization. The existing exact derived comparisons and adjunction mate formulas give
the same canonical maps directly. No false statement or target-signature defect was found.
The concrete model representation caused avoidable kernel expansion; the change record
explains the equivalent generic record and checks its consumers. A downstream search for
`ReductionModel` found only this module, including no external constructor/projection use.
No new DAG nodes were needed; the added public record is attached to the existing node.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
