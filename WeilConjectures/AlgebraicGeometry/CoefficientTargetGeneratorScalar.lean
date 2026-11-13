/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap

/-! # Scalar compatibility of supported coefficient generators

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientTarget_generator_scalar_ring
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (a : Γ(U.toScheme, ⊤)) :
    let r := (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top : Z ⟶ ⊤).op
      ((((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) a)
    X'.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
      (X'.presheaf.map (homOfLE hW.le).op
        (g'.app ((f ⁻¹ᵁ U).ι ''ᵁ Z) (((f ⁻¹ᵁ U).ι.appIso Z).inv r))) =
    X'.presheaf.map (homOfLE (inf_le_right : W ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B)).op
      (f'.app B (g.appLE ⊤ B (by simp) a))  := by
  dsimp only
  have hc : (Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop = (f ∣_ U).appTop := by
    simp [Scheme.toSpecΓ_appTop]
  rw [hc]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  let K := W ⊓ f' ⁻¹ᵁ B
  have hr : (f ∣_ U).appTop ≫
      (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top : Z ⟶ ⊤).op =
      (f ∣_ U).appLE ⊤ Z (by simp) := by
    simp [Scheme.Hom.appTop, Scheme.Hom.appLE, ← Functor.map_comp]
  have hv : (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top : Z ⟶ ⊤).op
      ((f ∣_ U).appTop a) = (f ∣_ U).appLE ⊤ Z (by simp) a := by
    simpa only [CommRingCat.comp_apply] using congrArg (fun k ↦ k a) hr
  change X'.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
      (X'.presheaf.map (homOfLE hW.le).op
        (g'.app ((f ⁻¹ᵁ U).ι ''ᵁ Z)
          ((f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top : Z ⟶ ⊤).op
            ((f ∣_ U).appTop a)))) = _
  rw [hv]
  simp only [morphismRestrict_appLE]
  simp only [← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  erw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  simp only [w]
  have hi : U.ι.appLE (U.ι ''ᵁ ⊤) ⊤ (by simp) = 𝟙 _ := by
    simp [Scheme.Opens.ι_appLE]
  have ht := Scheme.Hom.appLE_comp_appLE (f' ≫ g) U.ι (U.ι ''ᵁ ⊤) ⊤ K
    (by simp) (by simp)
  rw [hi, Category.id_comp] at ht
  exact congrArg (fun k ↦ k a) ht.symm


/-- The supported pullback-unit section is linear over the global ring of U.
Only scalar compatibility is asserted; neither affineness nor bijectivity is needed
(Stacks, Tags 0096 and 0097). -/
theorem coefficientTarget_generator_scalar
    {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules)
    (U : T.Opens)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ (a : Γ(U.toScheme, ⊤)) (s : N),
      (coefficientSupportIso f' M W B).inv
        (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (a • s))) =
      (algebraMap Γ(U.toScheme, ⊤) Γ(T', B) a) •
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) := by
  classical
  dsimp only
  intro a s
  let M := (pullback g').obj F
  let e := coefficientSupportIso f' M W B
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [coefficientSupportIso_smul, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  let r := (f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top : Z ⟶ ⊤).op
    ((((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) a)
  have hs : (a • s : (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))) =
      r • (show Γ(F.restrict (f ⁻¹ᵁ U).ι, Z) from s) := rfl
  have hunit (b : Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ Z))
      (t : Γ(F, (f ⁻¹ᵁ U).ι ''ᵁ Z)) :
      ((pullbackPushforwardAdjunction g').unit.app F).app ((f ⁻¹ᵁ U).ι ''ᵁ Z)
          (b • t) =
        g'.app ((f ⁻¹ᵁ U).ι ''ᵁ Z) b •
          (show Γ(M, g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) from
            ((pullbackPushforwardAdjunction g').unit.app F).app ((f ⁻¹ᵁ U).ι ''ᵁ Z) t) :=
    Hom.app_smul _ b t
  rw [hs]
  simp only [coefficientPullbackGenerator, smul_restrictAppIso_hom_apply,
    hunit, map_smul]
  congr 1
  exact coefficientTarget_generator_scalar_ring f U Z g g' f' w W hW B a

end
end AlgebraicGeometry.Scheme.Modules
