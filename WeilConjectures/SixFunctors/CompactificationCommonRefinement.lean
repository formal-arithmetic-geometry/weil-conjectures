/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.NatIso
import WeilConjectures.Compactification.Cofiltered

/-! # Comparison through common compactification refinements

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, paragraphs 1 and 3, the common-refinement argument.
(blueprint: lem-fix-compactification-common-refinement-comparison).

The proof uses only common refinements, simultaneous equalization, composition,
and cancellation. The geometric cofilteredness instance is a private proof import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

private theorem cofiltered_comparison
    {C D : Type*} [Category C] [Category D] [IsCofilteredOrEmpty C]
    (F : C → D) (ρ : ∀ {a b : C}, (a ⟶ b) → (F b ⟶ F a))
    (hcomp : ∀ {a b c : C} (r : a ⟶ b) (s : b ⟶ c), ρ (r ≫ s) = ρ s ≫ ρ r)
    (hiso : ∀ {a b : C} (r : a ⟶ b), IsIso (ρ r)) :
    ∃ τ : ∀ a b, F a ≅ F b,
      (∀ a b d (r : d ⟶ a) (s : d ⟶ b), (τ a b).hom ≫ ρ s = ρ r) ∧
      (∀ a, τ a a = Iso.refl _) ∧
      (∀ a b c, τ a b ≪≫ τ b c = τ a c) ∧
      (∀ σ : ∀ a b, F a ≅ F b,
        (∀ a b d (r : d ⟶ a) (s : d ⟶ b), (σ a b).hom ≫ ρ s = ρ r) → σ = τ) := by
  classical
  have : ∀ {a b : C} (r : a ⟶ b), IsIso (ρ r) := hiso
  let τ (a b : C) : F a ≅ F b :=
    asIso (ρ (IsCofiltered.minToLeft a b)) ≪≫
      (asIso (ρ (IsCofiltered.minToRight a b))).symm
  have hτ (a b d : C) (r : d ⟶ a) (s : d ⟶ b) :
      (τ a b).hom ≫ ρ s = ρ r := by
    obtain ⟨e, α, β, hleft, hright⟩ := IsCofiltered.bowtie
      (IsCofiltered.minToLeft a b) r (IsCofiltered.minToRight a b) s
    apply (cancel_mono (ρ β)).1
    simp only [Category.assoc]
    rw [← hcomp β s, ← hright, hcomp]
    simp only [τ, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← hcomp, hleft, hcomp]
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · intro a
    apply Iso.ext
    apply (cancel_mono (ρ (𝟙 a))).1
    simpa using hτ a a a (𝟙 a) (𝟙 a)
  · intro a b c
    let d := IsCofiltered.min a (IsCofiltered.min b c)
    let r : d ⟶ a := IsCofiltered.minToLeft _ _
    let s : d ⟶ b := IsCofiltered.minToRight _ _ ≫ IsCofiltered.minToLeft b c
    let t : d ⟶ c := IsCofiltered.minToRight _ _ ≫ IsCofiltered.minToRight b c
    apply Iso.ext
    apply (cancel_mono (ρ t)).1
    simp only [Iso.trans_hom, Category.assoc, hτ b c d s t, hτ a b d r s,
      hτ a c d r t]
  · intro σ hσ
    funext a b
    apply Iso.ext
    apply (cancel_mono (ρ (IsCofiltered.minToRight a b))).1
    rw [hσ a b _ (IsCofiltered.minToLeft a b),
      hτ a b _ (IsCofiltered.minToLeft a b)]

/-- Restrict an invertible-on-inputs refinement system before forming comparisons.
Source: step 11 of the parent compactification-reindexing proof.
(blueprint: lem-fix-compactification-common-refinement-comparison).
Proof: whisker every refinement by the input functor. Whiskering preserves composition,
and componentwise invertibility makes the whiskered transformations invertible. Apply
the cofiltered comparison argument in the functor category and evaluate its normalization
at each input. Natural-transformation extensionality converts componentwise uniqueness
back to uniqueness of the whole family. -/
theorem compactification_common_refinement_on_inputs
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {A C D : Type*} [Category A] [Category C] [Category D]
    (ι : A ⥤ C) (F : Compactification f → C ⥤ D)
    (ρ : ∀ {a b : Compactification f}, (a ⟶ b) → (F b ⟶ F a))
    (hcomp : ∀ {a b c : Compactification f} (r : a ⟶ b) (s : b ⟶ c),
      ρ (r ≫ s) = ρ s ≫ ρ r)
    (hiso : ∀ {a b : Compactification f} (r : a ⟶ b) (K : A),
      IsIso ((ρ r).app (ι.obj K))) :
    ∃ τ : ∀ a b, ι ⋙ F a ≅ ι ⋙ F b,
      (∀ a b d (r : d ⟶ a) (s : d ⟶ b) (K : A),
        (τ a b).hom.app K ≫ (ρ s).app (ι.obj K) = (ρ r).app (ι.obj K)) ∧
      (∀ a, τ a a = Iso.refl _) ∧
      (∀ a b c, τ a b ≪≫ τ b c = τ a c) ∧
      (∀ σ : ∀ a b, ι ⋙ F a ≅ ι ⋙ F b,
        (∀ a b d (r : d ⟶ a) (s : d ⟶ b) (K : A),
          (σ a b).hom.app K ≫ (ρ s).app (ι.obj K) = (ρ r).app (ι.obj K)) → σ = τ) := by
  let ρ' {a b : Compactification f} (r : a ⟶ b) := Functor.whiskerLeft ι (ρ r)
  have hcomp' {a b c : Compactification f} (r : a ⟶ b) (s : b ⟶ c) :
      ρ' (r ≫ s) = ρ' s ≫ ρ' r := by
    dsimp only [ρ']
    rw [hcomp, Functor.whiskerLeft_comp]
  have hiso' {a b : Compactification f} (r : a ⟶ b) : IsIso (ρ' r) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro K
    exact hiso r K
  obtain ⟨τ, hτ, hid, htrans, huniq⟩ :=
    cofiltered_comparison (fun c ↦ ι ⋙ F c) ρ'
      (fun r s ↦ hcomp' r s) (fun r ↦ hiso' r)
  refine ⟨τ, ?_, hid, htrans, ?_⟩
  · intro a b d r s K
    exact congrArg (fun t ↦ t.app K) (hτ a b d r s)
  · intro σ hσ
    apply huniq σ
    intro a b d r s
    ext K
    exact hσ a b d r s K

end
