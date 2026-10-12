/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionShift

/-!
# The derived exchange transformation is a morphism of triangulated functors

Let `u : U ⟶ V` be a morphism of schemes. On the bounded below derived categories of étale
sheaves, the derived direct image `R u_*⁺` is a triangulated functor, with the shift isomorphism
obtained by comparing injective resolutions
(`AlgebraicGeometry.Etale.isTriangulated_rightDerivedFunctorPlus_lowerStar`, blueprint
`lem-weil-pbc-derived-direct-image-triangulated`), and the derived adjunction
`u^* ⊣ R u_*⁺` is compatible with the shifts
(`AlgebraicGeometry.Etale.commShift_upperStarLowerStarAdjunction_derivedPlus`, blueprint
`lem-weil-pbc-derived-adjunction-commshift`).

For a commutative square of schemes `g' ≫ f = f' ≫ g`, the derived exchange transformation
`Ex : Φ = R f_*⁺ ⋙ D g^*⁺ ⟶ Ψ = D g'^*⁺ ⋙ R f'_*⁺`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`) commutes with the composite shift
isomorphisms of `Φ` and `Ψ` (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_app_shift`), and
hence its components on the three vertices of a triangle form a morphism from the image of the
triangle under `Φ` to its image under `Ψ`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlusTriangle`). This is blueprint
`lem-weil-pbc-derived-exchange-triangulated`. The shift compatibility itself is the instance
`AlgebraicGeometry.Etale.commShift_derivedBaseChangeMapPlus`; the morphism of triangles is
`CategoryTheory.NatTrans.mapTriangle` (blueprint
`lem-weil-pbc-commshift-nattrans-triangle-morphism`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

section DirectImage

variable {U V : Scheme.{u}} (u : U ⟶ V)

omit [HasSmallSiteSheafify A] in
/-- This is blueprint `lem-weil-pbc-derived-direct-image-triangulated`: the derived direct image
`R u_*⁺ : D⁺(U_ét) ⥤ D⁺(V_ét)` is a triangulated functor, for its shift isomorphism
`R u_*⁺(K⟦1⟧) ≅ (R u_*⁺ K)⟦1⟧` obtained from injective resolutions (the general instance
`CategoryTheory.Functor.rightDerivedFunctorPlus` of an additive functor). -/
lemma Etale.isTriangulated_rightDerivedFunctorPlus_lowerStar :
    ((u)_*[A]).rightDerivedFunctorPlus.IsTriangulated :=
  inferInstance

/-- This is blueprint `lem-weil-pbc-derived-adjunction-commshift` for étale sheaves: the derived
adjunction `u^* ⊣ R u_*⁺` on the bounded below derived categories is compatible with the
shifts, i.e. its unit and counit commute with the shift isomorphisms
(`CategoryTheory.Adjunction.derivedPlus_unit_app_shift`,
`CategoryTheory.Adjunction.derivedPlus_counit_app_shift`). -/
lemma Etale.commShift_upperStarLowerStarAdjunction_derivedPlus :
    (Etale.upperStarLowerStarAdjunction A u).derivedPlus.CommShift ℤ :=
  inferInstance

end DirectImage

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g)

/-- The composite `Φ = R f_*⁺ ⋙ D g^*⁺` is a triangulated functor (blueprint
`lem-weil-pbc-triangulated-functor-composite`, Mathlib's
`CategoryTheory.Functor.IsTriangulated.instComp`). -/
lemma Etale.isTriangulated_rightDerivedFunctorPlus_lowerStar_comp_upperStar :
    ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).IsTriangulated :=
  inferInstance

/-- The composite `Ψ = D g'^*⁺ ⋙ R f'_*⁺` is a triangulated functor (blueprint
`lem-weil-pbc-triangulated-functor-composite`). -/
lemma Etale.isTriangulated_upperStar_comp_rightDerivedFunctorPlus_lowerStar :
    (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus).IsTriangulated :=
  inferInstance

omit [HasSmallSiteSheafify A] in
/-- This is blueprint `lem-weil-pbc-derived-exchange-triangulated` (1): the derived exchange
transformation commutes with the shift isomorphisms `ξ` of `Φ = R f_*⁺ ⋙ D g^*⁺` and `ζ` of
`Ψ = D g'^*⁺ ⋙ R f'_*⁺`, i.e. `ζ_K ∘ Ex_{K⟦n⟧} = Ex_K⟦n⟧ ∘ ξ_K` for every `n : ℤ`. -/
@[reassoc]
lemma Etale.derivedBaseChangeMapPlus_app_shift
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (n : ℤ) :
    (((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).commShiftIso n).hom.app
        K ≫ ((Etale.derivedBaseChangeMapPlus A sq).app K)⟦n⟧' =
      (Etale.derivedBaseChangeMapPlus A sq).app (K⟦n⟧) ≫
        ((((g')^*[A]).mapDerivedCategoryPlus ⋙
          (f')_*[A].rightDerivedFunctorPlus).commShiftIso n).hom.app K :=
  NatTrans.shift_app_comm _ n K

omit [HasSmallSiteSheafify A] in
/-- This is blueprint `lem-weil-pbc-derived-exchange-triangulated` (2): the derived exchange
transformation induces, for every triangle `T` of `D⁺(X_ét)`, a morphism of triangles
`Φ(T) ⟶ Ψ(T)` with components the exchange maps on the three vertices of `T`, naturally in
`T`. -/
noncomputable def Etale.derivedBaseChangeMapPlusTriangle :
    ((f)_*[A].rightDerivedFunctorPlus ⋙ ((g)^*[A]).mapDerivedCategoryPlus).mapTriangle ⟶
      (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus).mapTriangle :=
  NatTrans.mapTriangle (Etale.derivedBaseChangeMapPlus A sq)

omit [HasSmallSiteSheafify A] in
@[simp]
lemma Etale.derivedBaseChangeMapPlusTriangle_app_hom₁
    (T : Triangle (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))) :
    ((Etale.derivedBaseChangeMapPlusTriangle A sq).app T).hom₁ =
      (Etale.derivedBaseChangeMapPlus A sq).app T.obj₁ :=
  rfl

omit [HasSmallSiteSheafify A] in
@[simp]
lemma Etale.derivedBaseChangeMapPlusTriangle_app_hom₂
    (T : Triangle (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))) :
    ((Etale.derivedBaseChangeMapPlusTriangle A sq).app T).hom₂ =
      (Etale.derivedBaseChangeMapPlus A sq).app T.obj₂ :=
  rfl

omit [HasSmallSiteSheafify A] in
@[simp]
lemma Etale.derivedBaseChangeMapPlusTriangle_app_hom₃
    (T : Triangle (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))) :
    ((Etale.derivedBaseChangeMapPlusTriangle A sq).app T).hom₃ =
      (Etale.derivedBaseChangeMapPlus A sq).app T.obj₃ :=
  rfl

end Exchange

end AlgebraicGeometry
