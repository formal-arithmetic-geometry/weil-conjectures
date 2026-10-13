/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Colimit comparisons along cones, and a five lemma for them

Let `c` be a cone over a cofiltered diagram `D : I ⥤ B`, and let `N` be a family of abelian
groups on `B` with restriction maps `ρ g : N T →+ N T'` for `g : T' ⟶ T`. The proposition
`CategoryTheory.Limits.Cone.IsColimitRestriction c N ρ` says that the restriction maps
`N (D i) → N c.pt` exhibit `N c.pt` as the colimit of the `N (D i)`, elementwise: every element
of `N c.pt` comes from some `N (D i)`, and an element of `N (D i)` vanishing in `N c.pt` already
vanishes in some `N (D j)`, `j ⟶ i`.

For families `M K` depending on objects `K` of a pretriangulated category, functorially and with
long exact sequences, this property satisfies a five lemma along distinguished triangles
(`CategoryTheory.Limits.Cone.isColimitRestriction_obj₂`): the filtered colimit of exact
sequences of abelian groups is exact.
-/

@[expose] public section

namespace CategoryTheory.Limits.Cone

open Pretriangulated

variable {I : Type*} [Category* I] {B : Type*} [Category* B] {D : I ⥤ B} (c : Cone D)

/-- The restriction maps `ρ (c.π.app i) : N (D.obj i) →+ N c.pt` exhibit `N c.pt` as the colimit
of the `N (D.obj i)`, elementwise: every element of `N c.pt` comes from some `N (D.obj i)`, and an
element of `N (D.obj i)` which vanishes in `N c.pt` already vanishes in some `N (D.obj j)`. -/
def IsColimitRestriction (N : B → Type*) [∀ T, AddCommGroup (N T)]
    (ρ : ∀ {T T' : B}, (T' ⟶ T) → N T →+ N T') : Prop :=
  (∀ x : N c.pt, ∃ (i : I) (y : N (D.obj i)), ρ (T' := c.pt) (c.π.app i) y = x) ∧
    ∀ (i : I) (y : N (D.obj i)), ρ (T' := c.pt) (c.π.app i) y = 0 →
      ∃ (j : I) (g : j ⟶ i), ρ (D.map g) y = 0

variable {c}

/-- A family of trivial groups satisfies the colimit property. -/
lemma isColimitRestriction_of_subsingleton (N : B → Type*) [∀ T, AddCommGroup (N T)]
    (ρ : ∀ {T T' : B}, (T' ⟶ T) → N T →+ N T') [Nonempty I] [∀ T, Subsingleton (N T)] :
    c.IsColimitRestriction N ρ :=
  ⟨fun _ ↦ ⟨Classical.arbitrary I, 0, Subsingleton.elim _ _⟩,
    fun i _ _ ↦ ⟨i, 𝟙 i, Subsingleton.elim _ _⟩⟩

/-- The colimit property is transported along bijections compatible with the restriction
maps. -/
lemma IsColimitRestriction.of_bijective {N N' : B → Type*} [∀ T, AddCommGroup (N T)]
    [∀ T, AddCommGroup (N' T)] {ρ : ∀ {T T' : B}, (T' ⟶ T) → N T →+ N T'}
    {ρ' : ∀ {T T' : B}, (T' ⟶ T) → N' T →+ N' T'} (h : c.IsColimitRestriction N ρ)
    (β : ∀ T, N T →+ N' T) (hβ : ∀ T, Function.Bijective (β T))
    (hβρ : ∀ {T T' : B} (g : T' ⟶ T) (x : N T), ρ' g (β T x) = β T' (ρ g x)) :
    c.IsColimitRestriction N' ρ' := by
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := (hβ _).2 x
    obtain ⟨i, y, rfl⟩ := h.1 x
    exact ⟨i, β _ y, hβρ _ _⟩
  · obtain ⟨y, rfl⟩ := (hβ _).2 y
    rw [hβρ, ← map_zero (β c.pt)] at hy
    obtain ⟨j, g, hg⟩ := h.2 i y ((hβ _).1 hy)
    exact ⟨j, g, by rw [hβρ, hg, map_zero]⟩

variable {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- **Five lemma for colimit comparisons.** Let `M K` be families of abelian groups on `B`,
indexed by the objects `K` of a pretriangulated category, with restriction maps `ρ K`
(functorial along composition) and actions `act f` of the morphisms `f : K ⟶ L` (commuting with
the restriction maps), such that every distinguished triangle induces sequences
`M K₁ T → M K₂ T → M K₃ T` exact in the middle. If the colimit property holds for the outer
vertices `K₁, K₃` of a distinguished triangle and for `K₁⟦1⟧` and `K₃⟦-1⟧`, it holds for the
middle vertex `K₂`. -/
lemma isColimitRestriction_obj₂ [IsCofiltered I] (M : 𝒟 → B → Type*)
    [∀ K T, AddCommGroup (M K T)] (ρ : ∀ (K : 𝒟) {T T' : B}, (T' ⟶ T) → M K T →+ M K T')
    (act : ∀ {K L : 𝒟} (_ : K ⟶ L) (T : B), M K T →+ M L T)
    (hρ : ∀ (K : 𝒟) {T T' T'' : B} (g : T' ⟶ T) (h : T'' ⟶ T') (x : M K T),
      ρ K h (ρ K g x) = ρ K (h ≫ g) x)
    (hact : ∀ {K L : 𝒟} (f : K ⟶ L) {T T' : B} (g : T' ⟶ T) (x : M K T),
      ρ L g (act f T x) = act f T' (ρ K g x))
    (hexact : ∀ (Tr : Triangle 𝒟) (_ : Tr ∈ distTriang 𝒟) (T : B) (x : M Tr.obj₂ T),
      act Tr.mor₂ T x = 0 ↔ ∃ y, act Tr.mor₁ T y = x)
    (Tr : Triangle 𝒟) (hTr : Tr ∈ distTriang 𝒟)
    (h₁ : c.IsColimitRestriction (M Tr.obj₁) (ρ _)) (h₃ : c.IsColimitRestriction (M Tr.obj₃) (ρ _))
    (h₁' : c.IsColimitRestriction (M (Tr.obj₁⟦(1 : ℤ)⟧)) (ρ _))
    (h₃' : c.IsColimitRestriction (M (Tr.obj₃⟦(-1 : ℤ)⟧)) (ρ _)) :
    c.IsColimitRestriction (M Tr.obj₂) (ρ _) := by
  have ex := hexact _ hTr
  have rot := hexact _ (rot_of_distTriang _ hTr)
  obtain ⟨w', hw'⟩ : ∃ w' : Tr.obj₃⟦(-1 : ℤ)⟧ ⟶ Tr.obj₁, w' = Tr.invRotate.mor₁ := ⟨_, rfl⟩
  have inv (T : B) (x : M Tr.obj₁ T) : act Tr.mor₁ T x = 0 ↔ ∃ y, act w' T y = x := by
    subst hw'
    exact hexact _ (inv_rot_of_distTriang _ hTr) T x
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, y₃, hy₃⟩ := h₃.1 (act Tr.mor₂ c.pt x)
    have hw : ρ _ (T' := c.pt) (c.π.app i) (act Tr.mor₃ (D.obj i) y₃) = 0 := by
      rw [hact, hy₃]
      exact (rot c.pt _).2 ⟨x, rfl⟩
    obtain ⟨j, g, hg⟩ := h₁'.2 i _ hw
    rw [hact] at hg
    obtain ⟨z₂, hz₂⟩ : ∃ z : M Tr.obj₂ (D.obj j), act Tr.mor₂ _ z = ρ _ (D.map g) y₃ :=
      (rot (D.obj j) _).1 hg
    have hx : act Tr.mor₂ c.pt (x - ρ _ (T' := c.pt) (c.π.app j) z₂) = 0 := by
      rw [map_sub, ← hact]
      erw [hz₂]
      rw [hρ, c.w, hy₃, sub_self]
    obtain ⟨x₁, hx₁⟩ := (ex c.pt _).1 hx
    obtain ⟨k, y₁, hy₁⟩ := h₁.1 x₁
    refine ⟨IsCofiltered.min j k, ρ _ (D.map (IsCofiltered.minToLeft j k)) z₂ +
      act Tr.mor₁ _ (ρ _ (D.map (IsCofiltered.minToRight j k)) y₁), ?_⟩
    rw [map_add, hρ, c.w, hact, hρ, c.w, hy₁]
    erw [hx₁]
    exact add_sub_cancel _ _
  · have h₂₃ : ρ _ (T' := c.pt) (c.π.app i) (act Tr.mor₂ _ y) = 0 := by
      rw [hact, hy, map_zero]
    obtain ⟨j, g, hg⟩ := h₃.2 i _ h₂₃
    rw [hact] at hg
    obtain ⟨z, hz⟩ := (ex _ _).1 hg
    have h₀ : act Tr.mor₁ c.pt (ρ _ (T' := c.pt) (c.π.app j) z) = 0 := by
      rw [← hact, hz, hρ, c.w, hy]
    obtain ⟨x', hx'⟩ := (inv c.pt _).1 h₀
    obtain ⟨k, y', hy'⟩ := h₃'.1 x'
    have h₄ : ρ _ (T' := c.pt) (c.π.app (IsCofiltered.min j k))
        (ρ _ (D.map (IsCofiltered.minToLeft j k)) z -
          act w' _
            (ρ _ (D.map (IsCofiltered.minToRight j k)) y')) = 0 := by
      rw [map_sub, hρ, c.w, hact, hρ, c.w, hy', hx', sub_self]
    obtain ⟨m, e, he⟩ := h₁.2 _ _ h₄
    refine ⟨m, e ≫ IsCofiltered.minToLeft j k ≫ g, ?_⟩
    rw [map_sub, sub_eq_zero, hρ, hact, hρ] at he
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← hρ, ← hz, hact, he]
    exact (inv _ _).2 ⟨_, rfl⟩

end CategoryTheory.Limits.Cone
