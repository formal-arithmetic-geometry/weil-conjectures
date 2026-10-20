# Scheduled upstream sync e9ba49ac4 -> 5f7b33eac (2026-10-20T08:30:31Z)

## Reason

Routine sync with slopmaster2 (168 commits; ~/cc1/upsync-quick.py, the human 2026-10-20).

## Old

upstream base e9ba49ac4dbf8bd5104c3e8b0109030fa6d3cf3d

## New

upstream base 5f7b33eac44235eeaa18609df41a933e867c6af4; merge conflict 1, imports 2, merged 1, source-proof 1, take 279

Conflicts resolved:

- `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean`: ours kept (upstream-statement-exceptions.tsv)

## Users

302 Lean file(s) changed by the merge and the canonical migration; 1085 node record(s) re-pointed by the migration.

## Status

landed

## Prefer upstream, round 1

The upstream module(s) `WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.SubalgebraLimit` failed here while identical to the tip: the upstream files of their environment that this sync had merged with changes of ours take the tip's file: `WeilConjectures.AlgebraicGeometry.Cohomology.Serre`, `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing`, `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality`, `WeilConjectures.AlgebraicGeometry.EffectiveDescent`, `WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`, `WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent`, `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, `WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`, `WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement`, `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic`, `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field`, `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`, `WeilConjectures.AlgebraicGeometry.Picard.Representability`, `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`, `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic`, `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`, `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality`, `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`, `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, `WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit`, `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable`, `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`, `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`, `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`, `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`, `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex`, `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc`, `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`, `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`, `WeilConjectures.RingTheory.HopfAlgebra.Cartier`, `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`, `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`, `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.

## Prefer upstream, round 2

The upstream module(s) `WeilConjectures.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization` failed here while identical to the tip: the upstream files of their environment that this sync had merged with changes of ours take the tip's file: `WeilConjectures.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization`, `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange`.

## Aborted (2026-10-20T09:24:31Z)

the failures reach Weil.Solution (the six target statements, never changed) through Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization

Every landing of the run was dropped; the library is the one from before the sync.

## Status

reverted
