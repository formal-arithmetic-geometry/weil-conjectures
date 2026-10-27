## What changed

Proved `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.derived_restriction_localization`
without changing any public declaration signature, definition, instance, or public import.
This is a partial delivery for the five-hole module, as permitted for a module with several
sorries. The other four theorem bodies remain exactly `by sorry`.

Five proved private helpers establish the ordinary global-section composition identity,
identify the derived pushforward compositor as an adjunction conjugate, calculate the
composite derived unit, derive the global-section composition identity, and combine these
into `restriction_comp`. The localization equation follows by applying `restriction_comp`
to `k ≫ a` and `a' ≫ t`, transporting across `w.w`, and cancelling the two pullback
compositors. No localization invertibility is used. This proves the existing statement
with all its original binders; the argument in fact only needs the square's commutativity.

Added four private proof imports: `RightDerivedFunctor.CompConjugate`, module-object
`UpperLowerStar.Coherence`, finite-coefficient `Derived.LowerStarComp` (the generic derived
composition associativity lemma), and finite-coefficient `UpperLowerStar.Restriction`
(the ordinary global-section composition lemma). All are under `WeilConjectures`.

Validation: the completed proof compiled in 32.5 seconds before import pruning.
`#print axioms derived_restriction_localization` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary print command was removed.
The final pruned file is checked again by the delivery compile and preflight.

## Proved and sorry left

Closed 1 original hole and added 0 holes. No split-off statements or new modules.

Proved:

- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.derived_restriction_localization`

The following 4 original holes remain, each belonging to
`lem-sfb-closed-test-derived-exchange-model`, with its original source and proof docstring:

- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_test_naturality`
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.section_comparison_base_change_naturality`
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_coefficient_naturality`
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_derived_exchange_model`

## No longer needed

Removed the following 22 private imports unused by the completed restriction proof.
Public imports are retained verbatim, so importers see the same public interface.

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
- `WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
- `Sheaf.Paper.RingedDerivedSliceLocalization`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`

No DAG node or entire module is withdrawn. In particular, all five declared proof dependencies
remain needed for the four untouched obligations and their unit route; this delivery does not
claim that the whole model or its normalization dependencies are pruned. The removed private
imports were the old broad proof context; foundational declarations needed by the statements
continue to arrive through the public imports.

## Where the brief, the DAG or earlier work was wrong

The geometric localization clause of the assigned module is stronger in scope than the
restricted clause exported by `ClosedTestLocalizedModelData.GeometricCoherence`: that clause
requires the map to be heterogeneously equal to a specific closed-fibre map. Directly applying
it cannot prove the assigned arbitrary-map localization theorem. The completed elementary
adjunction-composition proof handles that scope without changing either statement.

There is also an import-direction obstacle to using several planned model dependencies:
`ClosedTestChainMateRestriction`, `ClosedTestLocalizedModelData` (and hence its coherence
modules), and `ClosedTestScalarComparisonMaps` currently import the assigned module for its
canonical map definitions. An extraction experiment confirmed that the definitions can be
shared, but introduced module-boundary typeclass issues with the cached monoidal structures.
No extraction or consumer edit is included here. The remaining obligations have not been
relabelled as new lemmas and no assumptions have been introduced to conceal this obstacle.

A separate direct proof attempt expressed section comparisons as derived restrictions followed
by square/counit maps and attempted a pullback-compositor pasting calculation. Its additional
coherence elaboration exceeded the file's 60-second limit. Those experimental helpers and
profiling options are absent from this packet; the completed restriction proof does not use them.
The localization proof follows the argument already written in its original docstring, so no
DAG proof-route or unit-route change is claimed.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
