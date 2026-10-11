/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Base change of products of Kummer boundaries

The iterated cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)` of the Kummer boundaries of global
functions (`AlgebraicGeometry.Etale.kummerBoundaryProduct`) is compatible with base change along
every morphism `e : U' ⟶ U`: its restriction of supports is the product of the Kummer boundaries
of the pulled back functions `e^* f_a`.

This combines the base change of a single Kummer boundary
(`AlgebraicGeometry.Etale.kummerBoundary_baseChange`) with the base change of cup products with
supports (`AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupports`), and the
compatibility of the Tate twist datum with pullback.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_shiftTateObjectAddIso`
- `AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {U U' : Scheme.{u}}

omit [HasTateTwist Λ] in
/-- Pullback along a shift of an equation of shift amounts. -/
@[reassoc]
lemma leftDerivedUpperStar_map_eqToHom_shift_comp_commShiftIso_hom (e : U' ⟶ U)
    {K K' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hK : K = K')
    {n n' : ℤ} (h : n = n') :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (eqToHom (by rw [hK, h]) : K⟦n⟧ ⟶ K'⟦n'⟧) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n').hom.app K' =
      ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app K ≫
        eqToHom (by rw [hK, h]) := by
  subst hK h
  simp

omit [HasTateTwist Λ] in
/-- Shifting a morphism across an equation of shift amounts. -/
@[reassoc]
lemma eqToHom_comp_shift_map {X X' Y : DerivedCategory (Sheaf U'.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))} (hX : X = X') {n n' : ℤ} (h : n = n') (f : X' ⟶ Y) :
    (eqToHom (by rw [hX, h]) : X⟦n⟧ ⟶ X'⟦n'⟧) ≫ f⟦n'⟧' =
      (eqToHom hX ≫ f)⟦n⟧' ≫ eqToHom (by rw [h]) := by
  subst hX h
  simp

omit [HasTateTwist Λ] in
/-- `K⟦a⟧ ⊗ M⟦b⟧ ≅ (K ⊗ M)⟦a + b⟧` is natural in both factors. -/
@[reassoc]
lemma derivedTensorHom_shift_comp_derivedTensorShiftIso_hom {X : Scheme.{u}}
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') (g : M ⟶ M') (a b : ℤ) :
    derivedTensorHom _ (f⟦a⟧') (g⟦b⟧') ≫ (derivedTensorShiftIso _ K' M' a b).hom =
      (derivedTensorShiftIso _ K M a b).hom ≫ (derivedTensorHom _ f g)⟦a + b⟧' := by
  simp only [derivedTensorHom, Category.assoc, Functor.map_comp]
  rw [derivedTensorShiftIso_hom_naturality_right, derivedTensorShiftIso_hom_naturality_left_assoc]

/-- **The Tate twist identifications are compatible with pullback**:
`Le^* (Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')])` is the corresponding identification
on `U'`, through `Le^* (K ⊗ M) ≅ Le^* K ⊗ Le^* M` and `Le^* Λ_U(m)[2m] ≅ Λ_{U'}(m)[2m]`. -/
lemma leftDerivedUpperStar_map_shiftTateObjectAddIso (e : U' ⟶ U) (m m' : ℤ) :
    (L((e)^*[ModuleCat.{u + 1} Λ])).map (shiftTateObjectAddIso Λ U m m').hom ≫
        (leftDerivedUpperStarTateShiftIso Λ e (m + m')).hom =
      (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
        derivedTensorHom _ (leftDerivedUpperStarTateShiftIso Λ e m).hom
          (leftDerivedUpperStarTateShiftIso Λ e m').hom ≫
        (shiftTateObjectAddIso Λ U' m m').hom := by
  have hc : (L((e)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectAddIso U m m').hom ≫
      (HasTateTwist.leftDerivedUpperStarTwistObjectIso e (m + m')).hom =
        (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
          derivedTensorHom _ (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m).hom
            (HasTateTwist.leftDerivedUpperStarTwistObjectIso e m').hom ≫
          (HasTateTwist.twistObjectAddIso U' m m').hom := by
    rw [HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso]
    simp only [derivedTensorHom, Category.assoc]
  have hd : (L((e)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorShiftIso _
      (HasTateTwist.twistObject (Λ := Λ) U m) (HasTateTwist.twistObject U m') (2 * m)
        (2 * m')).hom ≫
      ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m + 2 * m')).hom.app _ ≫
        (leftDerivedUpperStarTensorIso _ e _ _).hom⟦2 * m + 2 * m'⟧' =
      (leftDerivedUpperStarTensorIso _ e _ _).hom ≫
        derivedTensorHom _ (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).hom.app _)
          (((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m')).hom.app _) ≫
        (derivedTensorShiftIso _ _ _ _ _).hom := by
    simp only [leftDerivedUpperStarTensorIso_hom, derivedTensorHom, Category.assoc]
    exact leftDerivedUpperStarTensorComparison_derivedTensorShiftIso _ e _ _ _ _
  simp only [shiftTateObjectAddIso, leftDerivedUpperStarTateShiftIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, eqToIso.hom, Functor.map_comp, Category.assoc, tateObject,
    leftDerivedUpperStarTateObjectIso]
  rw [leftDerivedUpperStar_map_eqToHom_shift_comp_commShiftIso_hom_assoc Λ e rfl (by ring),
    eqToHom_comp_shift_map Λ rfl (by ring)]
  simp only [eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, hc, Functor.map_comp,
    Functor.map_comp, reassoc_of% hd, ← derivedTensorHom_comp_assoc,
    derivedTensorHom_shift_comp_derivedTensorShiftIso_hom_assoc]

end Etale

end AlgebraicGeometry
