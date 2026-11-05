/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.SupportsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# The triangle of sections with support on module objects, and filtered colimits

Let `Λ` be a commutative condensed ring such that `Λ_X = condensedRingObj Λ X` is flat, and
`j : U ⟶ X` a quasi-compact open immersion. On module objects over `Λ_X`, the short complex of
functors `Γ_Z ⟶ 𝟭 ⟶ j_* j^*` (`ProEtale.CondensedRing.sectionsWithSupportShortComplex`) is short
exact on injective objects: the restriction `I ⟶ j_* j^* I` of an injective module object is an
epimorphism (`ProEtale.CondensedRing.epi_upperStarLowerStarAdjunction_unit_app_of_injective`), so
its right derived functors form a natural distinguished triangle
`RΓ_Z K ⟶ K ⟶ Rj_* j^* K ⟶`.

The cohomology sheaves of the last two terms, evaluated on module objects placed in degree `0`,
commute with `u + 1`-small filtered colimits: for `j_* j^*` because the higher direct images of
abelian pro-étale sheaves along a quasi-compact quasi-separated morphism do
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`, blueprint
`det-pe-bounded-continuity-direct-image`), and the underlying abelian sheaves of the derived
pushforward of module objects are the derived pushforward of the underlying abelian sheaves
(`ProEtale.CondensedRing.rightDerivedLowerStarCompMapDerivedCategoryForgetIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X)

variable [IsOpenImmersion j] [PreservesFiniteLimits (tensorLeft (condensedRingObj Λ X))]

variable [QuasiCompact j]

end AlgebraicGeometry.ProEtale.CondensedRing
