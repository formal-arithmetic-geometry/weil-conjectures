/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapFiniteFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-!
# Multiplication by constant global sections of `C(-, T')`

For a continuous homomorphism `T → T'` of commutative topological rings and `t : T'`, the
`T̲`-linear map `T̲ ⟶ T̲'`, `x ↦ x t` (`Profinite.continuousMapSMulRightHom`), is the structure
morphism `T̲ ⟶ T̲'` followed by the action of the constant global section `t` of `T̲'`
(`Profinite.continuousMapSMulRightHom_hom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace Profinite

variable {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T'] [Algebra T T']
  (hφ : Continuous (algebraMap T T'))

/-- The unit of `T̲` followed by `x ↦ x t` is the constant global section `t` of `T̲'`. -/
lemma one_hom_comp_continuousMapSMulRightHom_hom (t : T') :
    (continuousMapConstRingHom.{u} T 1).hom ≫ (continuousMapSMulRightHom hφ t).hom =
      (continuousMapConstRingHom T' t).hom := by
  refine Sheaf.hom_ext_of_ε_comp ?_
  rw [Functor.map_comp, ← Category.assoc, continuousMapConstRingHom, continuousMapConstRingHom,
    Sheaf.ε_comp_ringHomΓSheafCompose_hom, Sheaf.ε_comp_ringHomΓSheafCompose_hom]
  · ext X ⟨m⟩
    have key : ((continuousMapSMulRightHom hφ t).hom.hom.app X).hom
        ((m : (continuousMapRingPresheaf.{u} T).obj X) * continuousMapConstSectionRingHom T X 1) =
        (m : (continuousMapRingPresheaf.{u} T').obj X) *
          continuousMapConstSectionRingHom T' X t := by
      refine ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)
      simp only [continuousMapSMulRightHom, continuousMapConstSectionRingHom]
      erw [continuousMapAbMap_app_apply, ULift.mul_down, ULift.mul_down, ULift.down_intCast,
        ULift.down_intCast]
      simp
    exact key
  all_goals exact fun _ _ ↦ rfl

/-- The `T̲`-linear map `T̲ ⟶ T̲'`, `x ↦ x t`, is the structure morphism `T̲ ⟶ T̲'` followed by
the action of the constant global section `t` of `T̲'`. -/
lemma continuousMapSMulRightHom_hom (t : T') :
    (continuousMapSMulRightHom.{u} hφ t).hom = continuousMapRingObjAlgebraMap hφ ≫
      Mod.smulHom (continuousMapConstRingHom T' t) (Mod.regular _) := by
  have h₁ := Mod.act_hom (continuousMapSMulRightHom.{u} hφ t)
  have h₂ := one_hom_comp_continuousMapSMulRightHom_hom hφ t
  rw [map_one, Γ.one_hom] at h₂
  rw [Mod.act_comap_obj] at h₁
  calc (continuousMapSMulRightHom.{u} hφ t).hom
      = (ρ_ _).inv ≫ _ ◁ η[continuousMapRingObj.{u} T] ≫ μ[continuousMapRingObj.{u} T] ≫
          (continuousMapSMulRightHom.{u} hφ t).hom := by
        rw [MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]
    _ = (ρ_ _).inv ≫ _ ◁ (continuousMapConstRingHom T' t).hom ≫
          continuousMapRingObjAlgebraMap hφ ▷ _ ≫ μ[continuousMapRingObj.{u} T'] := by
        erw [h₁]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, h₂]
        rfl
    _ = _ := by
        rw [Mod.smulHom]
        erw [Mod.leftUnitor_inv_comp_whiskerRight_comp_mul (R := continuousMapRingObj.{u} T')]
        rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

end Profinite
