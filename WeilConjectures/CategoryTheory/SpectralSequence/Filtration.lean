/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Tactic.Linarith

/-!
# Decreasing filtrations by subobjects

A decreasing filtration of an object `A` of an abelian category is a family of subobjects
`Fᵖ A` (`p : ℤ`) with `Fᵖ⁺¹ A ≤ Fᵖ A`; its graded pieces are `grᵖ A = Fᵖ A / Fᵖ⁺¹ A`, the
cokernels of the inclusions. A morphism `φ : A ⟶ A'` is compatible with filtrations if it maps
`Fᵖ A` into `Fᵖ A'`; it then induces maps on the steps and on the graded pieces.

The main result is the *finite filtration induction*
`CategoryTheory.DecreasingFiltration.isIso_of_isIso_grMap`: a morphism of objects with finite
filtrations which is an isomorphism on all graded pieces is an isomorphism.

## Main definitions

- `CategoryTheory.DecreasingFiltration`: decreasing `ℤ`-filtrations (`def-sp-filtration`).
- `CategoryTheory.DecreasingFiltration.gr`: the graded pieces.
- `CategoryTheory.DecreasingFiltration.IsFinite`: finite filtrations.
- `CategoryTheory.DecreasingFiltration.image`: the image filtration along a morphism
  (`def-sp-image-filtration`).
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- A decreasing filtration `⋯ ⊇ Fᵖ A ⊇ Fᵖ⁺¹ A ⊇ ⋯` of an object `A` by subobjects, indexed
by `p : ℤ`. This is blueprint `def-sp-filtration`. -/
structure DecreasingFiltration (A : C) where
  /-- The `p`-th step `Fᵖ A` of the filtration. -/
  F (p : ℤ) : Subobject A
  antitone : Antitone F

namespace DecreasingFiltration

variable {A : C} (F : DecreasingFiltration A)

omit [Abelian C] in
lemma le_of_le {p q : ℤ} (h : p ≤ q) : F.F q ≤ F.F p := F.antitone h

/-- The inclusion `Fᵖ⁺¹ A ⟶ Fᵖ A` (for `p + 1 = p'`). -/
noncomputable def incl (p p' : ℤ) (h : p + 1 = p' := by lia) : (F.F p' : C) ⟶ F.F p :=
  Subobject.ofLE _ _ (F.le_of_le (by lia))

instance (p p' : ℤ) (h : p + 1 = p') : Mono (F.incl p p' h) := by
  dsimp [incl]; infer_instance

/-- The graded piece `grᵖ A = Fᵖ A / Fᵖ⁺¹ A` (blueprint `def-sp-filtration`). -/
noncomputable def gr (p : ℤ) : C := cokernel (F.incl p (p + 1))

/-- The projection `Fᵖ A ⟶ grᵖ A`. -/
noncomputable def grπ (p : ℤ) : (F.F p : C) ⟶ F.gr p := cokernel.π _

instance (p : ℤ) : Epi (F.grπ p) := by dsimp [grπ]; infer_instance

/-- The short exact sequence `0 ⟶ Fᵖ⁺¹ A ⟶ Fᵖ A ⟶ grᵖ A ⟶ 0`. -/
noncomputable def grSc (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (F.incl p (p + 1)) (F.grπ p) (cokernel.condition _)

lemma grSc_shortExact (p : ℤ) : (F.grSc p).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := by dsimp [grSc]; infer_instance
  epi_g := by dsimp [grSc]; infer_instance

/-- A filtration is *finite* if it is `⊤` in all sufficiently small degrees and `⊥` in all
sufficiently large degrees. -/
def IsFinite : Prop :=
  (∃ m : ℤ, ∀ p ≤ m, F.F p = ⊤) ∧ (∃ N : ℤ, ∀ p ≥ N, F.F p = ⊥)

/-- The image filtration `Fᵖ B = im (Fᵖ A ⟶ B)` along a morphism `u : A ⟶ B`
(blueprint `def-sp-image-filtration`). -/
noncomputable def image {B : C} (u : A ⟶ B) : DecreasingFiltration B where
  F p := (Subobject.exists u).obj (F.F p)
  antitone _ _ h := (Subobject.exists u).monotone (F.antitone h)

section Hom

variable {A' : C} {F} {F' : DecreasingFiltration A'}

/-- A morphism `φ : A ⟶ A'` is compatible with the filtrations if `φ (Fᵖ A) ⊆ Fᵖ A'` for all
`p`, i.e. it is a morphism of filtered objects. -/
def IsCompatible (F : DecreasingFiltration A) (F' : DecreasingFiltration A') (φ : A ⟶ A') :
    Prop :=
  ∀ p, (F'.F p).Factors ((F.F p).arrow ≫ φ)

variable {φ : A ⟶ A'} (hφ : IsCompatible F F' φ)

/-- The map `Fᵖ A ⟶ Fᵖ A'` induced by a compatible morphism. -/
noncomputable def stepMap (p : ℤ) : (F.F p : C) ⟶ F'.F p :=
  (F'.F p).factorThru _ (hφ p)

omit [Abelian C] in
@[reassoc (attr := simp)]
lemma stepMap_arrow (p : ℤ) : stepMap hφ p ≫ (F'.F p).arrow = (F.F p).arrow ≫ φ :=
  Subobject.factorThru_arrow _ _ _

omit [Abelian C] in
@[reassoc (attr := simp)]
lemma incl_stepMap (p p' : ℤ) (h : p + 1 = p') :
    F.incl p p' h ≫ stepMap hφ p = stepMap hφ p' ≫ F'.incl p p' h := by
  rw [← cancel_mono (F'.F p).arrow]
  simp [incl]

/-- The map `grᵖ A ⟶ grᵖ A'` induced by a compatible morphism. -/
noncomputable def grMap (p : ℤ) : F.gr p ⟶ F'.gr p :=
  cokernel.map _ _ (stepMap hφ (p + 1)) (stepMap hφ p) (incl_stepMap hφ p (p + 1) rfl)

@[reassoc (attr := simp)]
lemma grπ_grMap (p : ℤ) : F.grπ p ≫ grMap hφ p = stepMap hφ p ≫ F'.grπ p := by
  simp [grπ, grMap]

/-- The morphism of short exact sequences `Fᵖ⁺¹ ⟶ Fᵖ ⟶ grᵖ` induced by a compatible
morphism. -/
@[simps]
noncomputable def grScMap (p : ℤ) : F.grSc p ⟶ F'.grSc p where
  τ₁ := stepMap hφ (p + 1)
  τ₂ := stepMap hφ p
  τ₃ := grMap hφ p
  comm₁₂ := (incl_stepMap hφ p (p + 1) rfl).symm
  comm₂₃ := (grπ_grMap hφ p).symm

lemma isIso_stepMap_of_eq_bot (p : ℤ) (h : F.F p = ⊥) (h' : F'.F p = ⊥) :
    IsIso (stepMap hφ p) := by
  have h₁ : IsZero (F.F p : C) := by rw [h]; exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
  have h₂ : IsZero (F'.F p : C) := by
    rw [h']; exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
  exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

omit [Abelian C] in
lemma isIso_of_isIso_stepMap (p : ℤ) (h : F.F p = ⊤) (h' : F'.F p = ⊤)
    [IsIso (stepMap hφ p)] : IsIso φ := by
  have : IsIso (F.F p).arrow := by rw [h]; infer_instance
  have : IsIso (F'.F p).arrow := by rw [h']; infer_instance
  have e : φ = inv (F.F p).arrow ≫ stepMap hφ p ≫ (F'.F p).arrow := by simp
  rw [e]
  infer_instance

/-- Finite filtration induction (blueprint `lem-sp-finite-filtration-induction`): a morphism of
objects with finite decreasing filtrations which induces isomorphisms on all graded pieces is
an isomorphism. The induction step is the short five lemma
`CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃`
(blueprint `lem-weil-pbc-short-five-lemma`). -/
theorem isIso_of_isIso_grMap (hF : F.IsFinite) (hF' : F'.IsFinite)
    (hgr : ∀ p, IsIso (grMap hφ p)) : IsIso φ := by
  obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := hF
  obtain ⟨⟨m', hm'⟩, ⟨N', hN'⟩⟩ := hF'
  have key : ∀ k : ℕ, ∀ p, p + k = max N N' → IsIso (stepMap hφ p) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact isIso_stepMap_of_eq_bot hφ _ (hN _ (by lia)) (hN' _ (by lia))
    | succ k ih =>
      intro p hp
      have h₁ : IsIso (grScMap hφ p).τ₁ := ih (p + 1) (by lia)
      have h₃ : IsIso (grScMap hφ p).τ₃ := hgr _
      exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (grScMap hφ p) (F.grSc_shortExact _)
        (F'.grSc_shortExact _)
  have := key (max N N' - min (min m m') (max N N')).toNat (min (min m m') (max N N'))
    (by lia)
  exact isIso_of_isIso_stepMap hφ (min (min m m') (max N N')) (hm _ (by lia)) (hm' _ (by lia))

end Hom

end DecreasingFiltration

end CategoryTheory
