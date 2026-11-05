/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb

/-!
# The derived closed pullback of module objects preserves countable products

Let `Λ` be a commutative condensed ring, `X` a quasi-compact quasi-separated scheme and
`i : Z ⟶ X` a closed immersion with quasi-compact open complement `j : U ⟶ X`. The derived
pullback `Li^* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Z})` on module objects preserves countable products
(`AlgebraicGeometry.ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl`).

Indeed, the pullback `i^*` of abelian pro-étale sheaves preserves all limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab_of_isCompl`), hence so does its
transport `mapMod(i^*)` to module objects, and the module pullback `(i)^*⟦Λ⟧` is `mapMod(i^*)`
followed by the extension of scalars along an isomorphism, i.e. a restriction of scalars. The
module pullback is exact, so `Li^*` is the levelwise functor `D((i)^*⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`); since
countable products of module objects are exact (repleteness,
`AlgebraicGeometry.ProEtale.CondensedRing.countableAB4Star_mod`), derived countable products are
computed degreewise and are preserved by the levelwise functor
(`CategoryTheory.Functor.preservesLimitsOfShape_discrete_mapDerivedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

end AlgebraicGeometry.ProEtale.CondensedRing
