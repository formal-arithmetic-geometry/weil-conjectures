## What changed

Proved `WeilConjectures.SfbHomFilteredColimit.scalarComparison_naturality` in
`Sheaf.Paper.DerivedInternalHomFilteredColimit`, without changing its statement.
The proof obtains the natural unit from the proved ordinary coefficient adjunction,
proves that the sheafified scalar-unit generators detect module maps, and applies
Hom-product extensionality. A private calculation proves naturality for arbitrary
complexes and a commuting augmentation square. The fixed functorial resolution units
supply that square in the public theorem. Every added private helper is proved.

Changed `WeilConjectures.coefficientHomComponent` in
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation` to name its existing projection
through `homComplexπ`. This is the same chosen projection: the existence proposition
in `homComplex_projections_exists` is precisely `Classical.choose_spec` of
`homComplex_exists`, with its chosen functor named. Proof irrelevance identifies
the two selection proofs. This avoids repeatedly expanding the large nested choice
specification in component calculations. No other definition or public signature changed.
The change record is `coord/changes/coefficientHomComponentProjectionAPI.md`.

Added private imports of `WeilConjectures.Algebra.Homology.HomComplexComponents` and
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction` to the item.
The projection module adds a public import of `HomComplexComponents`, needed by its
updated definition. The item's existing public imports are retained; the
`KFlatIndependentCoefficients` public import is grouped with them.

Updated the two existing DAG nodes' proof descriptions and dependencies for these
changes. All other proof steps, including the five unfinished claims' plans, remain.

Validation: both delivered modules compile through `lcompile.py`. The six other direct
consumers of `coefficientHomComponent` also compiled against the changed definition
without edits: `RingedInternalHomShiftOfUniverses`, `RingedSliceEvaluationTranspose`,
`RingedSiteDualityMaps`, `CoefficientHomZeroClass`, `DerivedAutomorphismHomEvaluation`,
and `SpecifiedHomScalarEvaluation`. Existing public declaration signatures were compared
with the repository originals and are unchanged. No source-library module was modified.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.SfbHomFilteredColimit.scalarComparison_naturality`.
This is a complete Lean proof from the existing normalized-comparison existence
statement and the proved ordinary coefficient adjunction, not a decomposition.
It retains the original logical dependency on `scalarComparison_existsUnique`.

Five original holes remain, unchanged, all attached to
`lem-sfb-dc-hom-filtered-colimit`:

- `WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique`
- `WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison`
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_existsUnique`
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso`
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction`

No holes were added and none were split off. The adapted projection module has zero
holes before and after this change. The net change in holes in the two delivered
modules is minus one.

## No longer needed

The direct scalar naturality proof needs neither a tensor-total adjunction nor a derived
scalar-adjunction comparison. It uses the actual ordinary scalar unit and Hom projections.
The following private imports were unused by the completed proofs and were removed:

- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`

No module or DAG node is withdrawn. The dependencies for the other five original holes
are retained in the node, so the removed imports do not claim those mathematical
results are globally unnecessary. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The strict scalar naturality clause can be proved directly
from its normalized component formula and the ordinary coefficient adjunction; the
larger derived adjunction route is unnecessary for that clause. The old projection
definition exposed a costly nested choice term instead of the existing projection API.
The replacement preserves its data and evaluation convention.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
