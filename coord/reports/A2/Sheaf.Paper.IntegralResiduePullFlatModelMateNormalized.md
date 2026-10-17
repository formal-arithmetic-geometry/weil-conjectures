## What changed

Repaired the duplicate-proof return by moving the complete scalar-mate calculation
from `Sheaf.Paper.IntegralResidueScalarCounitModel` into the upstream item
`Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized`, removing its old copies
from ScalarCounitModel in the same delivery. ScalarCounitModel now imports and
reuses `scalar_mate_counit` and `restrict_pull_fac`; both entry points are public.
All other moved helpers and cached instances remain private. This is a relocation
of existing complete proofs, not a second proof of those statements.

The item's unchanged normalized theorem postcomposes `scalar_mate_counit` with the
inverse counit supplied by `hC`, then uses associativity and `hom_inv_id`. The two
modules compile without warnings. Their unchanged direct consumers
`IntegralResiduePullFlatModelComparison` and `IntegralResidueScalarGeometryBridge`
also compile against the repaired modules. Their merged import graph has no cycle and their
declared theorem statements have no duplicate between the two delivered modules.
The landing import/duplicate checker passes for both modules against the complete
merged source overlay. The dry run passes preflight and axiom checks.
No data definition or existing public theorem signature changes.

ScalarCounitModel is unclaimed and is repaired under the unclaimed-module rule.
The change record is `coord/changes/A2-residue-mate-local-proof-calculations.md`.

## Proved and sorry left

Closed 1 of 1 original item holes:
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel_mate_normalized`.
Zero holes remain in either delivered module; zero holes were added or split off.
The existing complete proofs of `scalar_mate_counit` and `restrict_pull_fac` are
reused after relocation. ScalarCounitModel's `integralResidue_scalarCounit_model`
remains proved with the same statement and proof calculation.

## No longer needed

ScalarCounitModel no longer directly imports
`Sheaf.Paper.IntegralResiduePullSquareData`,
`Sheaf.Paper.IntegralResiduePullOrdinaryUnit`, or
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
It imports the shared calculation instead. These dependencies remain needed by the
item; no module is withdrawn or pruned from the global import closure.

Removed the old copies in ScalarCounitModel of `exactSquareFac`,
`exactSquareFacInv`, `liftedSquareFac`, `exactLeftSquareFac`, `transportedUnitFac`,
`mixedDerivedUnitFac`, `mateModel`, `naturalOrdinaryFac`, `reduction_unit_fac`,
`restrict_pull_fac`, `scalar_mate_counit`, and `cachedProofInstance1` through
`cachedProofInstance12`. Each occurs exactly once in the item. No planned
mathematical dependency of their calculation is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied the scalar-counit helpers but retained their original
copies; the landing checker correctly rejected the duplicate statements. Simply
importing ScalarCounitModel from the item would close the existing path
ScalarCounitModel -> TensorModel -> TensorPresentation -> PullSquare ->
PullSquareIsIso -> PullFlatModel -> PullFlatModelComparison -> this item.
The repair therefore moves the existing calculation upstream and removes its old
copies atomically, preserving the acyclic dependency direction. The retained
sandbox report had incorrectly described importing ScalarCounitModel; it is now
corrected. Both node attachments now name the module containing the moved proofs.

## New nodes

`new-integral-residue-scalar-mate-counit` records the already-proved scalar mate
identity moved into the item; it introduces no sorry. Its proof is the ordinary
unit identity, the derived unit factorization and the adjunction hom-equivalence.

`new-integral-residue-restrict-pull-counit-factorization` records the already-proved
exact restriction/pullback factorization moved into the item; it introduces no
sorry. It follows from exact derived-composition and localization factorization.
These two records were retained from the returned delivery; they are new relative
to the current main branch. The unit's realized statement and steps are unchanged.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
