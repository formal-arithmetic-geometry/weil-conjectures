/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Induction along finite filtrations

A morphism `f : A ⟶ B` of filtered objects of an abelian category restricts to morphisms
`Fᵖ A ⟶ Fᵖ B` and induces morphisms `grᵖ A ⟶ grᵖ B` on the graded pieces. If both filtrations
are finite and all the induced maps on graded pieces are isomorphisms, then `f` and all its
restrictions are isomorphisms.

## Main definitions

- `CategoryTheory.FilteredObject.restriction`: the restriction `Fᵖ A ⟶ Fᵖ B` of a morphism of
  filtered objects.
- `CategoryTheory.FilteredObject.gradedMap`: the induced morphism `grᵖ A ⟶ grᵖ B`.

## Main statements

- `CategoryTheory.FilteredObject.finite_filtration_induction`: a morphism of finitely filtered
  objects inducing isomorphisms on all graded pieces is an isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

/-- The restriction `Fᵖ A ⟶ Fᵖ B` of a morphism of filtered objects `f : A ⟶ B`.

(blueprint: `def-sp-filtration`) -/
noncomputable def restriction {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    (A.filtration.F p : C) ⟶ (B.filtration.F p : C) :=
  Classical.choose (f.preserves p)

omit [Abelian C] in
@[reassoc (attr := simp)]
lemma restriction_arrow {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    restriction f p ≫ (B.filtration.F p).arrow = (A.filtration.F p).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves p)

omit [Abelian C] in
@[reassoc (attr := simp)]
lemma restriction_naturality {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    Subobject.ofLE _ _ (A.filtration.F_succ_le p) ≫ restriction f p =
      restriction f (p + 1) ≫ Subobject.ofLE _ _ (B.filtration.F_succ_le p) := by
  simp [← cancel_mono (B.filtration.F p).arrow]

/-- The morphism `grᵖ A ⟶ grᵖ B` induced on graded pieces by a morphism of filtered objects.

(blueprint: `def-sp-filtration`) -/
noncomputable def gradedMap {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    A.filtration.gr p ⟶ B.filtration.gr p :=
  cokernel.desc _ (restriction f p ≫ cokernel.π _) (by
    rw [restriction_naturality_assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma π_gradedMap {A B : FilteredObject C} (f : Hom A B) (p : ℤ) :
    cokernel.π _ ≫ gradedMap f p = restriction f p ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

/-- A morphism of filtered objects induces a morphism `grᵖ A ⟶ grᵖ B` on graded pieces,
compatible with the projections `Fᵖ ⟶ grᵖ`.

(blueprint: `def-sp-filtration`) -/
theorem exists_gradedMap (A B : FilteredObject C) (f : Hom A B) (p : ℤ) :
    ∃ g : A.filtration.gr p ⟶ B.filtration.gr p,
      cokernel.π (Subobject.ofLE (A.filtration.F (p + 1))
        (A.filtration.F p) (A.filtration.antitone (by omega))) ≫ g =
        restriction f p ≫ cokernel.π (Subobject.ofLE (B.filtration.F (p + 1))
          (B.filtration.F p) (B.filtration.antitone (by omega))) :=
  ⟨gradedMap f p, cokernel.π_desc _ _ _⟩

/-- If `f` restricts to an isomorphism `Fᵖ⁺¹ A ≅ Fᵖ⁺¹ B` and induces an isomorphism
`grᵖ A ≅ grᵖ B`, then it restricts to an isomorphism `Fᵖ A ≅ Fᵖ B`. -/
lemma isIso_restriction_of_isIso_succ {A B : FilteredObject C} (f : Hom A B) (p : ℤ)
    [IsIso (restriction f (p + 1))] [IsIso (gradedMap f p)] : IsIso (restriction f p) := by
  let φ : ShortComplex.mk _ _ (cokernel.condition (Subobject.ofLE _ _
      (A.filtration.F_succ_le p))) ⟶ ShortComplex.mk _ _ (cokernel.condition
        (Subobject.ofLE _ _ (B.filtration.F_succ_le p))) :=
    { τ₁ := restriction f (p + 1)
      τ₂ := restriction f p
      τ₃ := gradedMap f p
      comm₁₂ := (restriction_naturality f p).symm
      comm₂₃ := (π_gradedMap f p).symm }
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    { exact := ShortComplex.exact_cokernel _ } { exact := ShortComplex.exact_cokernel _ }

/-- If `Fᵖ A = 0` and `Fᵖ B = 0`, then the restriction `Fᵖ A ⟶ Fᵖ B` is an isomorphism. -/
lemma isIso_restriction_of_eq_bot {A B : FilteredObject C} (f : Hom A B) {p : ℤ}
    (hA : A.filtration.F p = ⊥) (hB : B.filtration.F p = ⊥) : IsIso (restriction f p) :=
  isIso_of_source_target_iso_zero _ (Subobject.isoOfEq _ _ hA ≪≫ Subobject.botCoeIsoZero)
    (Subobject.isoOfEq _ _ hB ≪≫ Subobject.botCoeIsoZero)

/-- A morphism of finitely filtered objects inducing isomorphisms on all graded pieces is an
isomorphism, and so are all its restrictions `Fᵖ A ⟶ Fᵖ B`.

(blueprint: `lem-sp-finite-filtration-induction`) -/
theorem finite_filtration_induction (A B : FilteredObject C) (f : Hom A B)
    (hA : A.filtration.IsFinite) (hB : B.filtration.IsFinite)
    (hgraded : ∀ p : ℤ, IsIso (gradedMap f p)) :
    IsIso f.hom ∧ ∀ p : ℤ, IsIso (restriction f p) := by
  obtain ⟨nA, mA, hnA, hmA⟩ := hA
  obtain ⟨nB, mB, hnB, hmB⟩ := hB
  have hbot {q : ℤ} (hq : max mA mB ≤ q) : IsIso (restriction f q) :=
    isIso_restriction_of_eq_bot f
      (eq_bot_iff.2 (hmA ▸ A.filtration.antitone (le_of_max_le_left hq)))
      (eq_bot_iff.2 (hmB ▸ B.filtration.antitone (le_of_max_le_right hq)))
  have hdown (k : ℕ) : IsIso (restriction f (max mA mB - k)) := by
    induction k with
    | zero => exact hbot (by simp)
    | succ k ih =>
      have : IsIso (restriction f (max mA mB - (k + 1 : ℕ) + 1)) := by
        rwa [show max mA mB - ((k + 1 : ℕ) : ℤ) + 1 = max mA mB - k by push_cast; omega]
      exact isIso_restriction_of_isIso_succ f _
  have hres (p : ℤ) : IsIso (restriction f p) := by
    rcases le_or_gt (max mA mB) p with hp | hp
    · exact hbot hp
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, p = max mA mB - k := ⟨(max mA mB - p).toNat, by omega⟩
      exact hk ▸ hdown k
  refine ⟨?_, hres⟩
  have : IsIso (A.filtration.F (min nA nB)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top, eq_top_iff, ← hnA]
    exact A.filtration.antitone (min_le_left _ _)
  have : IsIso (B.filtration.F (min nA nB)).arrow := by
    rw [Subobject.isIso_arrow_iff_eq_top, eq_top_iff, ← hnB]
    exact B.filtration.antitone (min_le_right _ _)
  have : f.hom = inv (A.filtration.F (min nA nB)).arrow ≫ restriction f (min nA nB) ≫
      (B.filtration.F (min nA nB)).arrow := by
    simp
  rw [this]
  infer_instance

end FilteredObject

end CategoryTheory
