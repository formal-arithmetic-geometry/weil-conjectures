## What changed

In `Sheaf.Paper.ProEtaleConstantReductionTower`, proved quotient compatibility,
additivity of the strict reduction functor, and existence of its total left-derived
functor with the specified K-flat computation property. The last proof uses the
existing independent-coefficient K-flat resolutions, derived scalar extension,
exact scalar restriction, levelwise detection of quasi-isomorphisms, and the
resolving-class construction of a left-derived functor. Two proved private helpers,
`scalarReduction_map_quasiIso` and `kFlat_leftDerived_exists`, keep the coefficient
map, target category and additive functor abstract during kernel checking; they
introduce no public declarations or proof obligations.

Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
Retained `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` and all
original public imports. Removed unused private imports listed below. Added only
file-local irreducibility attributes to large chosen comparison definitions: this
prevents expensive unfolding while elaborating subsequent definitions. Every
existing declaration signature and every non-theorem body is unchanged. No source
library file, target statement, or consumer was adapted. The local attribute changes
are recorded in `coord/changes/B3-ProEtaleConstantReductionTower-elaboration.md`,
as requested by the first delivery preflight.

Updated step 1, its dependencies, and proof origin in
`lem-sp-completion-mate-comparison` to record the implemented resolving-class
argument. The later steps remain needed by the unfinished comparisons.

Validation: the final complete module compiled through `lcompile.py` in 55.1 seconds.
The unchanged live consumers `Sheaf.Paper.CompletedProjectionCoherence` and
`Sheaf.Paper.CompletedPullbackUnitTower` compiled against it in 9.7 and 12.0 seconds.
These are separate single-file compiles, not a library build. An import-only
axiom probe for the three filled declarations also compiled (1.7 seconds): it
reports the standard axioms plus `sorryAx` from existing unfinished dependencies.
This is a proof from the existing stated dependencies, not a claim that the
entire transitive axiom closure has been completed.

## Proved and sorry left

Closed 3 of the 10 original holes; added 0 holes and split off 0 statements.
All declarations below have node `lem-sp-completion-mate-comparison`.

Proved:

- `AlgebraicGeometry.Scheme.OrderedExchange.quotient_comm`.
- `AlgebraicGeometry.Scheme.OrderedExchange.reductionModule_additive`.
- `AlgebraicGeometry.Scheme.OrderedExchange.reduction_exists`.

The seven original holes left unchanged are:

- `AlgebraicGeometry.Scheme.OrderedExchange.step_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryAugmentation_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.augmentation_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryReductionPullInv_isIso`.
- `AlgebraicGeometry.Scheme.OrderedExchange.levelPullIso_transition`.
- `AlgebraicGeometry.Scheme.OrderedExchange.reductionPullIso_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.projection_isIso`.

The existing generic `completionMateComparison` reexport is unchanged and is not
counted as a newly closed hole. The proved existence theorem uses existing stated
results with their own proof obligations; this delivery does not claim those
upstream obligations are closed. There are no new public declarations or hollow definitions.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`.
- `Sheaf.Paper.CompletedPullbackAdjunction`.
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`.
- `Sheaf.Paper.ProjectionFormulaTotalization`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.

No module or node is withdrawn. These direct private imports are unnecessary for
the three implemented proofs and the existing definitions. Their mathematical
results can still be needed by the seven unfinished proofs or by the generic
comparison imported publicly; removal here does not establish that they are
outside the targets' dependency closure. Accordingly the node retains those
planned dependencies and all existing tool approvals.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The original-site layer must be preserved:
although its two live importers do not use all of it, the quarantined
`Sheaf.Paper.OrderedExchangeCoefficientComparison` uses its constructions. A
search restricted to live importers would incorrectly suggest it can be pruned.
The quarantined source and its dependencies are preserved, and no withdrawal is
proposed.

For elaboration performance, use the existing finite-limit and finite-colimit
preservation lemmas for scalar restriction rather than reconstructing exactness
through the underlying sheaf functor. Large nested chosen comparisons also need
file-local unfolding boundaries; no global transparency attributes were changed.
The first preflight requested a change record for these local commands (included
above). A subsequent compile exceeded 60 seconds; the private, proved helper
lemmas reduced the checking cost, and the complete module then compiled.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
