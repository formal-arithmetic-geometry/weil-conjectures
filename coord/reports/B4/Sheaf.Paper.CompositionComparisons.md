## What changed

Prove `AlgebraicGeometry.ProEtale.compositionComparisons_integral` by descending the
left tower compositor through the published fully faithful reduction and taking the
unique counit-preserving right-adjoint comparison. A proved private categorical helper
assembles all five integral laws. Existing public signatures and definitions are unchanged.

The left arrow is the preimage of the composite of `If.leftComparison`,
`Ig.leftComparison`, `alphaTower`, and `Ih.leftComparison.symm`. Its reduction equation
follows from `FullyFaithful.map_preimage`. The right arrow is `rightAdjointUniq` after
transporting `Ih.adjunction` along the left arrow. The existing private
`evaluated_compositor` calculation proves its right reduction formula by transposition;
no faithfulness of finite tower evaluation is used. The three integral realization
records supply both unit and counit normalizations needed by that calculation.

Source read: the current blueprint composition comparisons statement and proof (3),
the unit's composition-of-purity statement, and the published integral reconstruction
and adjunction declarations. The categorical argument works also for zero objects,
identity functors, and identity equivalence counits. It requires no geometric
hypothesis beyond those already furnishing the realization records.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.compositionComparisons_integral`
(node `det-sp-composition-comparisons`). One of the three original holes is closed;
zero new holes are introduced.

Unchanged holes in the item, both owned by `det-sp-composition-comparisons`:
- `AlgebraicGeometry.ProEtale.compositionComparisons_finite`.
- `AlgebraicGeometry.ProEtale.compositionComparisons_towers`.

The finite proof still needs construction and coefficient coherence of the normalized
finite left compositors. `finiteAdjointCompositorTransposes` assumes these inputs.
The tower theorem additionally needs one coherent family over all finite quotient
levels before `towerAdjointCompositorRealization` applies.

## No longer needed

The integral proof does not need `lem-sp-integral-compositor-limit-realization` or
its module `Sheaf.Paper.IntegralCompositorLimitRealization`: the realization records
already contain fully faithful reductions and their adjunction normalizations, so
ordinary full-faithfulness and the existing compositor transpose calculation suffice.
That module was not imported by the original item. Removed unused direct proof imports:
`Sheaf.Paper.FiniteAdjointCompositorTransposes`,
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.Paper.FiniteCompactSiteCoherence`,
`Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Paper.ComparisonPullbackExact`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Mathlib.AlgebraicGeometry.Noetherian`, and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`.
The existing public imports are preserved because the public structures and result
types use their interfaces. Most removed direct imports remain available through
that public closure; no claim of whole-library pruning is made for those modules.
The finite and tower dependency plans remain necessary while their proofs are unfinished.

## Where the brief, the DAG or earlier work was wrong

The integral realization lemma's extra `Space`/`TowerEdge`/`IntegralEdge` packaging is
unnecessary for this item's existing `SpIntegralAdjunction.Realization` interface.
No statement is disputed or changed, and no source-library module is edited.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
