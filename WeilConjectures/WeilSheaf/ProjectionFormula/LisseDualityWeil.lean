/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.DualPullbackWeil
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhom

/-!
# The morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)` is compatible with structure isomorphisms

For an automorphism `a` and sheaves `M`, `X` of `ℚ̄_ℓ`-modules with structure isomorphisms
`(a⁻¹)_* M ≅ M` and `(a⁻¹)_* X ≅ X`, the morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)`
(`CategoryTheory.Mod.tensorDualToIhom`) intertwines the induced structure isomorphisms of the
tensor product and of the internal hom.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/-- The monoidal algebra behind the compatibility of `x ⊗ φ ↦ (m ↦ x φ(m))` with structure
morphisms along a lax braided functor `F`. -/
lemma lax_rightAct_evaluation_comm (F : C ⥤ C) [F.LaxBraided] {X M D A : C}
    (ev : D ⊗ M ⟶ A) (actX : A ⊗ X ⟶ X) (u : F.obj A ⟶ A) (s : F.obj M ⟶ M)
    (sD : F.obj D ⟶ D) (t : F.obj X ⟶ X)
    (hev : (sD ⊗ₘ s) ≫ ev = μ F D M ≫ F.map ev ≫ u)
    (hact : μ F A X ≫ F.map actX ≫ t = (u ⊗ₘ t) ≫ actX) :
    (μ F X D ▷ F.obj M) ≫ μ F (X ⊗ D) M ≫
        F.map ((α_ X D M).hom ≫ X ◁ ev ≫ (β_ X A).hom ≫ actX) ≫ t =
      ((t ⊗ₘ sD) ⊗ₘ s) ≫ (α_ X D M).hom ≫ X ◁ ev ≫ (β_ X A).hom ≫ actX := by
  have key : F.obj X ◁ μ F D M ≫ F.obj X ◁ F.map ev ≫ (t ⊗ₘ u) =
      t ▷ (F.obj D ⊗ F.obj M) ≫ X ◁ ((sD ⊗ₘ s) ≫ ev) := by
    rw [hev, tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc, ← whisker_exchange,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.LaxMonoidal.associativity_assoc, ← μ_natural_right_assoc,
    Functor.LaxBraided.braided_assoc, hact, ← BraidedCategory.braiding_naturality_assoc,
    reassoc_of% key]
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

end CategoryTheory

namespace AlgebraicGeometry.ProEtale


variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

/-- The action on a sheaf of modules with a structure morphism `t : (a⁻¹)_* X ⟶ X`, along the
lax monoidal pushforward. -/
lemma lowerStar_μ_act_comp (a : T ≅ T) (X : AdicSheaf l T) (t : (a.inv)_*ᵃ[l].obj X ⟶ X) :
    Functor.LaxMonoidal.μ (a.inv)_*[WeilCoefficients.{u} l] (adicConstantSheaf l T) X.X ≫
        (a.inv)_*[WeilCoefficients.{u} l].map (Mod.act X.X) ≫ t.hom =
      ((adicConstantSheafLowerStarIso l a.symm).hom ⊗ₘ t.hom) ≫ Mod.act X.X := by
  have ht := Mod.act_hom t
  have hρ : Mod.act ((a.inv)_*ᵃ[l].obj X).X = adicConstantSheafToLowerStar l a.inv ▷ _ ≫
      Functor.LaxMonoidal.μ (a.inv)_*[WeilCoefficients.{u} l] (adicConstantSheaf l T) X.X ≫
        (a.inv)_*[WeilCoefficients.{u} l].map (Mod.act X.X) := rfl
  have hu : (adicConstantSheafLowerStarIso l a.symm).hom ≫ adicConstantSheafToLowerStar l a.inv =
      𝟙 _ := by
    have h := (adicConstantSheafLowerStarIso l a.symm).hom_inv_id
    rwa [adicConstantSheafLowerStarIso_inv] at h
  rw [tensorHom_def, Category.assoc, ← ht, hρ]
  simp only [Category.assoc]
  erw [← comp_whiskerRight_assoc, hu, id_whiskerRight,
    Category.id_comp]

/-- **The morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)` is compatible with structure isomorphisms**
`s : (a⁻¹)_* M ≅ M` and `t : (a⁻¹)_* X ≅ X`: it intertwines the induced structure morphisms of
the tensor product `X ⊗ M^∨` and of the internal hom `𝓗om(M, X)`. -/
lemma tensorDualToIhom_comm (a : T ≅ T) (M X : AdicSheaf l T) (s : (a.inv)_*ᵃ[l].obj M ≅ M)
    (t : (a.inv)_*ᵃ[l].obj X ⟶ X) :
    (a.inv)_*ᵃ[l].map (Mod.tensorDualToIhom M X) ≫
        ((adicLowerStarCompIhomIso l a.inv M).inv.app X ≫ (Mod.ihomMap s.inv).app _ ≫
          (AdicSheaf.ihom M).map t) =
      ((adicLowerStarTensorLeftIso l a.inv ((AdicSheaf.ihom M).obj (AdicSheaf.unit l T))).hom.app
          X ≫
        (Mod.tensorLeftMap ((adicLowerStarCompIhomIso l a.inv M).inv.app (AdicSheaf.unit l T) ≫
          (Mod.ihomMap s.inv).app _ ≫
          (AdicSheaf.ihom M).map (adicLowerStarUnitIso l a.symm).hom)).app _ ≫
        (Mod.tensorLeft _).map t) ≫ Mod.tensorDualToIhom M X := by
  rw [← cancel_epi ((adicLowerStarTensorLeftIso l a.inv
    ((AdicSheaf.ihom M).obj (AdicSheaf.unit l T))).inv.app X)]
  apply Mod.tensorLeft_obj_hom_ext
  apply Mod.hom_ext_of_evaluation
  set D := (AdicSheaf.ihom M).obj (AdicSheaf.unit l T)
  set F := (a.inv)_*[WeilCoefficients.{u} l]
  set sD := (adicLowerStarCompIhomIso l a.inv M).inv.app (AdicSheaf.unit l T) ≫
    (Mod.ihomMap s.inv).app _ ≫ (AdicSheaf.ihom M).map (adicLowerStarUnitIso l a.symm).hom
  have hT : Mod.tensorπ ((a.inv)_*ᵃ[l].obj X) ((a.inv)_*ᵃ[l].obj D) ≫
      ((adicLowerStarTensorLeftIso l a.inv D).inv.app X).hom =
        μ F X.X D.X ≫ F.map (Mod.tensorπ X D) := by
    rw [← cancel_mono ((adicLowerStarTensorLeftIso l a.inv D).hom.app X).hom, Category.assoc,
      ← Mod.comp_hom', Iso.inv_hom_id_app, Mod.id_hom']
    erw [Category.comp_id]
    rw [Category.assoc, adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom, IsIso.hom_inv_id_assoc]
  have hI := uncurryHom_ihomStr a.inv M X s t
  rw [Mod.uncurryHom] at hI
  have hψ := Mod.tensorπ_tensorDualToIhom_evaluation M X
  have hR : (Mod.tensorπ ((a.inv)_*ᵃ[l].obj X) ((a.inv)_*ᵃ[l].obj D) ≫
      ((Mod.tensorLeftMap sD).app ((a.inv)_*ᵃ[l].obj X) ≫ (Mod.tensorLeft D).map t ≫
        Mod.tensorDualToIhom M X).hom) ▷ M.X ≫ Mod.evaluation M X =
      (t.hom ⊗ₘ sD.hom) ▷ M.X ≫ Mod.tensorDualToIhomAux M X := by
    rw [Mod.comp_hom', Mod.comp_hom', Mod.tensorπ_tensorLeftMap_assoc, Mod.tensorπ_map_assoc,
      ← Category.assoc (_ ◁ sD.hom), comp_whiskerRight_assoc, hψ, tensorHom_def']
  have hL : (Mod.tensorπ ((a.inv)_*ᵃ[l].obj X) ((a.inv)_*ᵃ[l].obj D) ≫
      ((adicLowerStarTensorLeftIso l a.inv D).inv.app X ≫
        (a.inv)_*ᵃ[l].map (Mod.tensorDualToIhom M X) ≫
        (adicLowerStarCompIhomIso l a.inv M).inv.app X ≫ (Mod.ihomMap s.inv).app _ ≫
          (AdicSheaf.ihom M).map t).hom) ▷ M.X ≫ Mod.evaluation M X =
      _ ◁ s.inv.hom ≫ μ F X.X D.X ▷ F.obj M.X ≫ μ F (X.X ⊗ D.X) M.X ≫
        F.map (Mod.tensorDualToIhomAux M X) ≫ t.hom := by
    have hT' : Mod.tensorπ ((a.inv)_*ᵃ[l].obj X) ((a.inv)_*ᵃ[l].obj D) ≫
        ((adicLowerStarTensorLeftIso l a.inv D).inv.app X).hom ≫
          ((a.inv)_*ᵃ[l].map (Mod.tensorDualToIhom M X)).hom =
        μ F X.X D.X ≫ F.map (Mod.tensorπ X D ≫ (Mod.tensorDualToIhom M X).hom) := by
      rw [← Category.assoc, hT, Functor.map_comp, Category.assoc]
      rfl
    rw [Mod.comp_hom' ((adicLowerStarTensorLeftIso l a.inv D).inv.app X),
      Mod.comp_hom' ((a.inv)_*ᵃ[l].map (Mod.tensorDualToIhom M X)), ← Category.assoc,
      ← Category.assoc, comp_whiskerRight_assoc, hI, Category.assoc, hT']
    erw [← whisker_exchange_assoc, comp_whiskerRight_assoc, μ_natural_left_assoc]
    rw [← Functor.map_comp_assoc, hψ]
    rfl
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hL, hR]
  have hev := ihomStr_tensorHom_comp_evaluation a.inv M (AdicSheaf.unit l T) s
    (adicLowerStarUnitIso l a.symm).hom
  have key := lax_rightAct_evaluation_comm (A := adicConstantSheaf l T) F
    (Mod.evaluation M (AdicSheaf.unit l T))
    (Mod.act X.X) (adicConstantSheafLowerStarIso l a.symm).hom s.hom.hom sD.hom t.hom hev
    (lowerStar_μ_act_comp a X t)
  have hs : s.inv.hom ≫ s.hom.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom']
  rw [Mod.tensorDualToIhomAux]
  erw [key]
  rw [tensorHom_def_assoc, ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    hs, MonoidalCategory.whiskerLeft_id, Category.id_comp]

end AlgebraicGeometry.ProEtale
