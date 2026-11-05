/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Inverse image of modules on small étale sites

Source: Stacks Project, Modules on Sites, Tags 03D1, 03D2 and 03D3
(blueprint: lem-weil-pbc-inverse-image-module-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restrict a hom equivalence to morphisms seen by faithful forgetful functors.
Source: Stacks Project, Tag 03D3, restriction and naturality step;
Mathlib `Adjunction.mkOfHomEquiv` and its unit/counit formulas
(blueprint: lem-weil-pbc-inverse-image-module-adjunction). -/
private theorem adjunctionOfLinearLifts
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (L : C ⥤ D) (R : D ⥤ C) (La : A ⥤ B) (Ra : B ⥤ A)
    (P : C ⥤ A) (Q : D ⥤ B) [P.Faithful] [Q.Faithful]
    (a : La ⊣ Ra) (e : L ⋙ Q ≅ P ⋙ La) (d : R ⋙ P ≅ Q ⋙ Ra)
    (hl : ∀ (G : C) (F : D) (alpha : La.obj (P.obj G) ⟶ Q.obj F),
      (∃ h : L.obj G ⟶ F, Q.map h = e.hom.app G ≫ alpha) ↔
        ∃ k : G ⟶ R.obj F, P.map k ≫ d.hom.app F = a.homEquiv _ _ alpha) :
    ∃ am : L ⊣ R,
      (∀ (G : C) (F : D) (h : L.obj G ⟶ F),
        P.map (am.homEquiv G F h) ≫ d.hom.app F =
          a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h)) ∧
      (∀ G : C, P.map (am.unit.app G) ≫ d.hom.app (L.obj G) =
        a.unit.app (P.obj G) ≫ Ra.map (e.inv.app G)) ∧
      (∀ F : D, Q.map (am.counit.app F) =
        e.hom.app (R.obj F) ≫ La.map (d.hom.app F) ≫ a.counit.app (Q.obj F)) := by
  classical
  let forward (G : C) (F : D) (h : L.obj G ⟶ F) : G ⟶ R.obj F :=
    Classical.choose ((hl G F (e.inv.app G ≫ Q.map h)).mp ⟨h, by simp⟩)
  have hf (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (forward G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) :=
    Classical.choose_spec ((hl G F (e.inv.app G ≫ Q.map h)).mp ⟨h, by simp⟩)
  have hi (G : C) (F : D) : Function.Injective (forward G F) := by
    intro h k hhk
    apply Q.map_injective
    have hh := congrArg (fun t ↦ P.map t ≫ d.hom.app F) hhk
    rw [hf, hf] at hh
    have hh' := (a.homEquiv _ _).injective hh
    simpa using congrArg (fun t ↦ e.hom.app G ≫ t) hh'
  have hs (G : C) (F : D) : Function.Surjective (forward G F) := by
    intro k
    obtain ⟨h, hh⟩ := (hl G F ((a.homEquiv _ _).symm
      (P.map k ≫ d.hom.app F))).mpr ⟨k, by simp⟩
    refine ⟨h, P.map_injective ((cancel_mono (d.hom.app F)).mp ?_)⟩
    rw [hf, hh]
    simp
  let E (G : C) (F : D) : (L.obj G ⟶ F) ≃ (G ⟶ R.obj F) :=
    Equiv.ofBijective (forward G F) ⟨hi G F, hs G F⟩
  have hE (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (E G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) := hf G F h
  have hleft {G' G : C} {F : D} (g : G' ⟶ G) (h : L.obj G ⟶ F) :
      E G' F (L.map g ≫ h) = g ≫ E G F h := by
    apply P.map_injective
    apply (cancel_mono (d.hom.app F)).mp
    rw [hE, P.map_comp, Category.assoc, hE, Q.map_comp]
    have he : La.map (P.map g) ≫ e.inv.app G = e.inv.app G' ≫ Q.map (L.map g) :=
      e.inv.naturality g
    rw [← Category.assoc, ← he, Category.assoc]
    exact a.homEquiv_naturality_left (P.map g) (e.inv.app G ≫ Q.map h)
  let core : Adjunction.CoreHomEquiv L R :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro G' G F g k
        apply (E G' F).injective
        rw [Equiv.apply_symm_apply, hleft, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro G F F' h k
        apply P.map_injective
        apply (cancel_mono (d.hom.app F')).mp
        have hd : P.map (R.map k) ≫ d.hom.app F' =
            d.hom.app F ≫ Ra.map (Q.map k) := d.hom.naturality k
        rw [hE, P.map_comp, Category.assoc, hd,
          ← Category.assoc, hE, Q.map_comp]
        simpa only [Category.assoc] using
          a.homEquiv_naturality_right (e.inv.app G ≫ Q.map h) (Q.map k) }
  let am := Adjunction.mkOfHomEquiv core
  have hm (G : C) (F : D) (h : L.obj G ⟶ F) :
      P.map (am.homEquiv G F h) ≫ d.hom.app F =
        a.homEquiv (P.obj G) (Q.obj F) (e.inv.app G ≫ Q.map h) := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    exact hE G F h
  refine ⟨am, hm, ?_, ?_⟩
  · intro G
    simpa [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] using hm G (L.obj G) (𝟙 _)
  · intro F
    have h := hm (R.obj F) F (am.counit.app F)
    have hc : am.homEquiv (R.obj F) F (am.counit.app F) = 𝟙 _ := by
      rw [← am.homEquiv_symm_id F, Equiv.apply_symm_apply]
    rw [hc, P.map_id, Category.id_comp] at h
    have h' := congrArg (fun t ↦ (a.homEquiv (P.obj (R.obj F)) (Q.obj F)).symm t) h
    simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h'
    simpa using congrArg (fun t ↦ e.hom.app (R.obj F) ≫ t) h'.symm

end AlgebraicGeometry
