## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`
by a complete two-variable finite-truncation argument. Its original public signature,
attributes and the source module's public imports are unchanged.

`Sheaf.AlgebraicGeometry.BoundedConstructibleHomPreservation` proves the categorical
reduction: exactness of tensor gives triangulatedness of its right adjoint in the second
variable, while the existing native contravariant exactness theorem handles the first
variable with the opposite triangulated shift. Two applications of the proved module-object
truncation induction reduce arbitrary bounded inputs to two constructible sheaves in degree zero.

`Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle` isolates the geometric degree-zero
finiteness assertion. Its inputs are abelian module objects, not arbitrary derived objects;
it does not assume the desired closure result or a repackaged version of it. The main proof
contains the actual two inductions, through the proved categorical reduction.

Unused private proof imports were removed. No coefficient interface or consumer was changed.

## Proved and sorry left

This is a decomposition, not a net proof: one original hole closed, one strictly smaller
geometric hole added, net zero holes among the changed files.

- Closed: `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`
  (`lem-sfb-dc-hom-small-coefficients`), by the two truncation inductions.
- Proved without a new hole:
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_closure`
  (`lem-sfb-dc-hom-devissage`).
- Original hole retained unchanged:
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`
  (`lem-sfb-dc-lower-star-preserves`).
- Added geometric hole:
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_hom_single`
  (`lem-sfb-dc-hom-single`). Its source and full coefficient-case proof are in the docstring
  and node. This is the degree-zero single-sheaf case of the finiteness theorem, including
  characteristic zero. The new categorical reduction has no sorry.

The existing imported theorem
`DerivedCategory.nativeInternalHom_contravariant_exact` remains a stated dependency;
this delivery does not claim to have proved that theorem or its source-variable cone calculation.

## No longer needed

The geometric coefficient comparisons of the original Hom route remain dependencies of
`lem-sfb-dc-hom-single`; none is declared mathematically obsolete. The direct-image node and
its dependencies are retained. No Lean declaration or module is withdrawn, and no unit
statement or realized proof step is bypassed.

Removed private imports from the assigned source module, because no remaining proof or
construction in that module uses them:

- `WeilConjectures.Algebra.Homology.KFlat`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`
- `WeilConjectures.CategoryTheory.DerivedCategory.Rationalization`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.IntegralLfpConstantModelComparison`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Sheaf.Paper.DerivedInternalHomFilteredColimit`
- `Sheaf.Paper.IntegralHomReduction`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`

These import removals are not a claim that every listed module leaves the targets' transitive
closure: other existing declarations may still use them.

## Where the brief, the DAG or earlier work was wrong

The original Hom plan is an assembly of nontrivial coefficient normalizations; it is not a
single usable internal-module theorem. Several lower coefficient interfaces import the
restricted six-functor module back through broad imports, which prevents using them in
this module without interface repairs. More significantly,
`integral_general_lfp_hom_finiteness` and `integralAdicInput_normalization` require
`Fact (ringChar k).Prime`, whereas the assigned public closedness instance only assumes
`ringChar k ≠ ell` and therefore includes characteristic zero. The public statement was
preserved. The degree-zero node explicitly records that full scope, and its proof uses
finite-coefficient finiteness with ell invertible, rather than treating positive
characteristic as an available hypothesis.

The new route separates the categorical bounded-complex argument from this geometric
input and records exactly which part remains. No target statement, definition or existing
public signature was changed.

## New nodes

`lem-sfb-dc-hom-devissage`: a completely proved two-variable truncation argument for the
native derived internal Hom, including its opposite triangulated shift structure.

`lem-sfb-dc-hom-single`: the separate geometric finiteness assertion for two constructible
sheaves in degree zero. It retains all four ell-adic coefficient constructors and the
characteristic-zero case. It is strictly a base case of the two finite inductions, not a
renaming of the arbitrary-complex closure theorem.

The existing `lem-sfb-dc-hom-small-coefficients` proof, proof dependencies and origin now
record this assembly. Preflight classified the filled public instance as an interface change despite its
unchanged signature. The requested change record is
`coord/changes/D4-bounded-constructible-hom-devissage.md`. The unit-route imports
CompletedCondensedCoefficients and CondensedModuleDerivedPushpull are retained.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
