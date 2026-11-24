/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Ext vanishing along a finite subobject filtration

If `Ext^q(-, N)` vanishes on the successive quotients of a finite filtration of `M` by
subobjects, then `Ext^q(M, N)` vanishes; similarly for `Ext^q(M, -)` and a finite filtration
of `N`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

private theorem subsingleton_of_source_iso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B N : C} {q : ℕ} (e : A ≅ B)
    (h : Subsingleton (Ext A N q)) : Subsingleton (Ext B N q) := by
  refine ⟨fun x y ↦ ?_⟩
  have hh := h.elim ((mk₀ e.hom).comp x (zero_add q))
    ((mk₀ e.hom).comp y (zero_add q))
  have hh' := congrArg (fun z ↦ (mk₀ e.inv).comp z (zero_add q)) hh
  simpa only [mk₀_comp_mk₀_assoc, e.inv_hom_id, mk₀_id_comp] using hh'

private theorem subsingleton_of_source_zero {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A N : C} {q : ℕ} (h : IsZero A) : Subsingleton (Ext A N q) := by
  have hz (x : Ext A N q) : x = 0 := by
    rw [← mk₀_id_comp x, h.eq_of_src (𝟙 A) 0, mk₀_zero, zero_comp]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- If `0 = F₀ ≤ ⋯ ≤ Fₙ = M` is a finite filtration of `M` by subobjects and `Ext^q(-, N)`
vanishes on each successive quotient `Fₐ₊₁ / Fₐ`, then `Ext^q(M, N)` vanishes. -/
theorem finiteSubobjectFiltration {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hquot : ∀ a : Fin n,
      Subsingleton (Ext (cokernel (Subobject.ofLE _ _ (hstep a))) N q)) :
    Subsingleton (Ext M N q) := by
  have hF (a : Fin (n + 1)) : Subsingleton (Ext (F a : C) N q) := by
    induction a using Fin.induction with
    | zero =>
      rw [hbot]
      exact subsingleton_of_source_zero
        (initialIsInitial.isZero.of_iso Subobject.botCoeIsoInitial)
    | succ a ih =>
      let f := Subobject.ofLE _ _ (hstep a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
      have hz (x : Ext (F a.succ : C) N q) : x = 0 := by
        obtain ⟨z, hz⟩ := contravariant_sequence_exact₂ hS N x (ih.elim _ _)
        rw [← hz, (hquot a).elim z 0, comp_zero]
      exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact subsingleton_of_source_iso
    (Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 M)) (hF _)

/-- Variant of `finiteSubobjectFiltration` in which the successive quotients of the filtration
of `M` are given up to isomorphism. -/
theorem finiteSubobjectFiltrationOfIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) (G : Fin n → C)
    (hiso : ∀ a : Fin n,
      Nonempty (cokernel (Subobject.ofLE _ _ (hstep a)) ≅ G a))
    (hquot : ∀ a : Fin n, Subsingleton (Ext (G a) N q)) :
    Subsingleton (Ext M N q) := by
  apply finiteSubobjectFiltration M N q n F hstep hbot htop
  intro a
  obtain ⟨e⟩ := hiso a
  exact subsingleton_of_source_iso e.symm (hquot a)

private theorem subsingleton_of_target_iso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B M : C} {q : ℕ} (e : A ≅ B)
    (h : Subsingleton (Ext M A q)) : Subsingleton (Ext M B q) := by
  refine ⟨fun x y ↦ ?_⟩
  have hh := h.elim (x.comp (mk₀ e.inv) (add_zero q))
    (y.comp (mk₀ e.inv) (add_zero q))
  have hh' := congrArg (fun z ↦ z.comp (mk₀ e.hom) (add_zero q)) hh
  simpa only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.inv_hom_id,
    comp_mk₀_id] using hh'

private theorem subsingleton_of_target_zero {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A M : C} {q : ℕ} (h : IsZero A) : Subsingleton (Ext M A q) := by
  have hz (x : Ext M A q) : x = 0 := by
    rw [← comp_mk₀_id x, h.eq_of_tgt (𝟙 A) 0, mk₀_zero, comp_zero]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- If `0 = F₀ ≤ ⋯ ≤ Fₙ = N` is a finite filtration of `N` by subobjects and `Ext^q(M, -)`
vanishes on objects isomorphic to the successive quotients `Fₐ₊₁ / Fₐ`, then `Ext^q(M, N)`
vanishes. -/
theorem finiteTargetSubobjectFiltrationOfIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject N)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) (G : Fin n → C)
    (hiso : ∀ a : Fin n,
      Nonempty (cokernel (Subobject.ofLE _ _ (hstep a)) ≅ G a))
    (hquot : ∀ a : Fin n, Subsingleton (Ext M (G a) q)) :
    Subsingleton (Ext M N q) := by
  have hQ (a : Fin n) :
      Subsingleton (Ext M (cokernel (Subobject.ofLE _ _ (hstep a))) q) := by
    obtain ⟨e⟩ := hiso a
    exact subsingleton_of_target_iso e.symm (hquot a)
  have hF (a : Fin (n + 1)) : Subsingleton (Ext M (F a : C) q) := by
    induction a using Fin.induction with
    | zero =>
      rw [hbot]
      exact subsingleton_of_target_zero
        (initialIsInitial.isZero.of_iso Subobject.botCoeIsoInitial)
    | succ a ih =>
      let f := Subobject.ofLE _ _ (hstep a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
      have hz (x : Ext M (F a.succ : C) q) : x = 0 := by
        obtain ⟨z, hz⟩ := covariant_sequence_exact₂ M hS x ((hQ a).elim _ _)
        rw [← hz, ih.elim z 0, zero_comp]
      exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact subsingleton_of_target_iso
    (Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 N)) (hF _)

end CategoryTheory.Abelian.Ext
