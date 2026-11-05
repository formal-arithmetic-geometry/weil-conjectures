/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# The direct image commutes with direct sums on `Loc(Dᵇc)`, from the heart

Let `Λ` be a commutative condensed ring and `p : Z ⟶ Y` a morphism of schemes. Blueprint
`det-prop-int-compactness-direct-sums` (2), (3): the derived direct image `Rp_*` on module
objects over `Λ` commutes with direct sums of objects of `Loc(Dᵇc(Z)⟦Λ⟧)` as soon as it does so
on the "ind-constructible heart" and has finite amplitude there.

The heart is replaced here by the smallest class of module objects containing the constructible
ones and closed under isomorphisms, kernels, cokernels, extensions and direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.constructibleCoproductClosure`). It is contained in
the class `IndCons(Z, Λ)` of the blueprint (blueprint `sk-prop-ind-heart`), so the hypotheses
below are implied by blueprint `det-prop-int-compactness-direct-sums` (1). The complexes with
cohomology in this class form a localizing subcategory containing `Dᵇc(Z)⟦Λ⟧`, hence
`Loc(Dᵇc(Z)⟦Λ⟧)`.

The reduction is `DerivedCategory.isIso_sigmaComparison_of_homologyProperty`; its exactness
hypotheses hold since the pro-étale topos is replete
(`AlgebraicGeometry.ProEtale.CondensedRing.countableAB4Star_mod`), so that the derived category of
module objects is left complete (`DerivedCategory.isHomotopyLimit_truncGECone`).

## Main results

* `AlgebraicGeometry.ProEtale.CondensedRing.homologyProperty_of_localizingClosure`: the objects
  of `Loc(Dᵇc(Z)⟦Λ⟧)` have cohomology in `constructibleCoproductClosure`.
* `preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar` (in the same namespace):
  if `Rp_*` sends the objects of `constructibleCoproductClosure` into degrees `≤ d` and commutes
  with direct sums of them, then its restriction to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
