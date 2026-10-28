/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Test
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

lemma mateEquiv_app_of_isoId_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C ⥤ E} {R₂ : E ⥤ C} {Lg : D ⥤ E} {Rg : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ag : Lg ⊣ Rg) {G : C ⥤ C} (I : G ≅ 𝟭 C)
    (c : L₂ ≅ L₁ ⋙ Lg) (θ : G ⋙ L₂ ⟶ L₁ ⋙ Lg)
    (hθ : ∀ B, θ.app B = L₂.map (I.hom.app B) ≫ c.hom.app B) (Y : D) :
    (mateEquiv a₁ a₂ θ).natTrans.app Y = I.hom.app (R₁.obj Y) ≫ R₁.map (ag.unit.app Y) ≫
      (conjugateIsoEquiv (a₁.comp ag) a₂ c).hom.app (Lg.obj Y) := by
  apply (a₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, hθ]
  simp only [conjugateIsoEquiv_apply_hom, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit]
  have h := c.hom.naturality (R₁.map (ag.unit.app Y))
  simp only [Functor.comp_obj, Functor.comp_map] at h
  simp [reassoc_of% h,Adjunction.comp_counit_app, ← Functor.map_comp_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Squares

variable {X Y Z : Scheme.{u}}

lemma pullbackSquareComparison_hom_app_comp_id_bottom (g' : X ⟶ Y) (p : Y ⟶ Z)
    (sq : CommSq g' (g' ≫ p) p (𝟙 Z))
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (pullbackSquareComparison Λ sq).hom.app B =
      L((g' ≫ p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Z).hom.app B) ≫
        (leftDerivedUpperStarComp Λ g' p).hom.app B := by
  have h := leftDerivedUpperStarComp_id_right_app Λ (g' ≫ p) B
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ (g' ≫ p) (𝟙 Z)).hom.app B),
    Iso.hom_inv_id_app_assoc, reassoc_of% h]

lemma pullbackSquareComparison_hom_app_comp_id_right (p' : X ⟶ Y) (g : Y ⟶ Z)
    (sq : CommSq (p' ≫ g) p' (𝟙 Z) g)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (pullbackSquareComparison Λ sq).hom.app A =
      (leftDerivedUpperStarComp Λ p' g).inv.app A ≫
        L((p' ≫ g)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Z).inv.app A) := by
  have h := leftDerivedUpperStarComp_id_right_app Λ (p' ≫ g) A
  rw [← cancel_mono (L((p' ≫ g)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Z).hom.app A))]
  simp only [pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc, h, ← Functor.map_comp, Iso.inv_hom_id_app,
    eqToHom_trans]
  simp

end Squares

namespace NearbyCyclesModel

variable {X X' G : Scheme.{u}}

lemma Hom.pullbackExchange_app_of_total_eq_id (N : NearbyCyclesModel X X')
    (g : G ⟶ N.generic) (e : G ⟶ X) (he : g ≫ N.ε = e)
    (φ : Hom ⟨N.total, G, g ≫ N.j, N.i, e⟩ N (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _)
    (hg : φ.generic = g)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (φ.pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((N.nearbyCycles Λ).obj A) ≫
        L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ g).unit.app
          (L((N.ε)^*⟦Λ⟧).obj A)) ≫
          (rightDerivedLowerStarComp Λ g N.j).hom.app (L((g)^*⟦Λ⟧).obj (L((N.ε)^*⟦Λ⟧).obj A)) ≫
          R((g ≫ N.j)_*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g N.ε).inv.app A ≫
            eqToHom (by rw [he]) ≫ L((e)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ X).inv.app A))) := by
  obtain ⟨total, generic, _, _, _⟩ := φ
  dsimp only at ht hg
  subst ht hg he
  have hj := mateEquiv_app_of_isoId_comp (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ (generic ≫ N.j))
    (derivedUpperStarLowerStarAdjunction Λ generic) (leftDerivedUpperStarId Λ N.total)
    (leftDerivedUpperStarComp Λ generic N.j)
    (pullbackSquareComparison Λ
      (⟨by simp⟩ : CommSq generic (generic ≫ N.j) N.j (𝟙 N.total))).hom
    (fun B ↦ pullbackSquareComparison_hom_app_comp_id_bottom Λ generic N.j _ B)
  simp only [Hom.pullbackExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, hj,
    pullbackSquareComparison_hom_app_id_right Λ N.i,
    pullbackSquareComparison_hom_app_comp_id_right Λ generic N.ε]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc, eqToHom_refl,
    Category.id_comp]
  rfl

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
