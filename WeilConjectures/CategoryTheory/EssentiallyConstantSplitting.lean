/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.EssentiallyConstantSystem
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Splitting an essentially constant inverse system

Source: Stacks Project, Homology, Lemma 12.31.5, Tag 070C, forward implication,
with the cone value of Categories, Tags 05PU(2) and 05PV
(blueprint: lem-weil-pbc-essentially-constant-splitting).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory.Functor

/-- Source: Stacks Project, Homology, Tag 070C, forward implication
(blueprint: lem-weil-pbc-essentially-constant-splitting).
The hypotheses are the explicit witnesses of `IsEssentiallyConstantWithValue F X`.
The natural index `n` represents the positive index `n + 1`. Put `p j = r ∘ t(j,i₀)`
and `Z j = ker (p j)` on the tail. The system splits into its cone value and these kernels.

Proof: (1) Iterate adjacent cone compatibility to obtain `t(j,i₀) ∘ π j = π i₀`
(def-weil-inverse-system, def-weil-pbc-essentially-constant-system). Compose with `r`:
`p j ∘ π j = id`, so `π j` is injective. For `c`, take `x = p j c` and
`z = c - π j x`. Then `p j z = 0`; applying `p j` to any decomposition determines
`x`, and cancellation determines `z` uniquely.
(2) Cone compatibility gives `t(k,j) ∘ π k = π j`. Functoriality of transitions gives
`p j ∘ t(k,j) = p k` (the same two dependency nodes). Thus transitions preserve kernels
and the two summands. Their restrictions inherit identity and composition from `F`.
(3) The factorization witness in def-weil-pbc-essentially-constant-system gives, for each
`j ≥ i₀`, a `k ≥ j` with `t(k,j) = π j ∘ p k`. It vanishes on `ker (p k)`. -/
theorem essentiallyConstant_splitting
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (X : AddCommGrpCat.{u})
    (π : ∀ n : ℕ, X ⟶ F.obj (op n))
    (hπ : ∀ n : ℕ, π (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op = π n)
    (i₀ : ℕ) (r : F.obj (op i₀) ⟶ X)
    (hr : π i₀ ≫ r = 𝟙 X)
    (hfactor : ∀ j : ℕ, ∃ k : ℕ, ∃ (hik : i₀ ≤ k) (hjk : j ≤ k),
      F.map (homOfLE hjk).op = F.map (homOfLE hik).op ≫ r ≫ π j) :
    let p : ∀ j : ℕ, i₀ ≤ j → (F.obj (op j) ⟶ X) :=
      fun _ hj ↦ F.map (homOfLE hj).op ≫ r
    let Z : ∀ j : ℕ, i₀ ≤ j → AddSubgroup (F.obj (op j)) :=
      fun j hj ↦ (p j hj).hom.ker
    (∀ (j : ℕ) (hj : i₀ ≤ j),
      π j ≫ p j hj = 𝟙 X ∧ Function.Injective (π j) ∧
      ∀ c : F.obj (op j),
        (∃! a : X × Z j hj, c = π j a.1 + (a.2 : F.obj (op j))) ∧
        ∀ a : X × Z j hj, c = π j a.1 + (a.2 : F.obj (op j)) → a.1 = p j hj c) ∧
    (∀ (j k : ℕ) (hj : i₀ ≤ j) (hjk : j ≤ k),
      F.map (homOfLE hjk).op ≫ p j hj = p k (hj.trans hjk) ∧
      π k ≫ F.map (homOfLE hjk).op = π j ∧
      (∀ z : Z k (hj.trans hjk),
        F.map (homOfLE hjk).op (z : F.obj (op k)) ∈ Z j hj) ∧
      ∀ (x : X) (z : Z k (hj.trans hjk)),
        F.map (homOfLE hjk).op (π k x + (z : F.obj (op k))) =
          π j x + F.map (homOfLE hjk).op (z : F.obj (op k))) ∧
    (∀ (j : ℕ) (hj : i₀ ≤ j), ∃ (k : ℕ) (hjk : j ≤ k),
      ∀ z : Z k (hj.trans hjk), F.map (homOfLE hjk).op (z : F.obj (op k)) = 0) := by
  have hcomp : ∀ {a b c : ℕ} (h₁ : b ≤ c) (h₂ : a ≤ b),
      F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE (h₂.trans h₁)).op := by
    intro a b c h₁ h₂
    rw [← F.map_comp]
    rfl
  have hπle : ∀ (i j : ℕ) (hij : i ≤ j), π j ≫ F.map (homOfLE hij).op = π i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl, F.map_id, Category.comp_id]
    | succ j hij ih =>
      rw [← hcomp (Nat.le_add_right j 1) hij, ← Category.assoc, hπ, ih]
  intro p Z
  have hp : ∀ (j : ℕ) (hj : i₀ ≤ j), π j ≫ p j hj = 𝟙 X := fun j hj ↦ by
    simp only [p]
    rw [← Category.assoc, hπle, hr]
  have hpx : ∀ (j : ℕ) (hj : i₀ ≤ j) (x : X), p j hj (π j x) = x := fun j hj x ↦ by
    rw [← ConcreteCategory.comp_apply, hp]
    rfl
  have hdec : ∀ (j : ℕ) (hj : i₀ ≤ j) (c : F.obj (op j)) (a : X × Z j hj),
      c = π j a.1 + (a.2 : F.obj (op j)) → a.1 = p j hj c := by
    intro j hj c a hc
    have h2 : p j hj (a.2 : F.obj (op j)) = 0 := a.2.2
    rw [hc, map_add, hpx, h2, add_zero]
  refine ⟨fun j hj ↦ ⟨hp j hj, fun x y hxy ↦ by rw [← hpx j hj x, hxy, hpx], fun c ↦ ?_⟩,
    fun j k hj hjk ↦ ?_, fun j hj ↦ ?_⟩
  · refine ⟨⟨⟨p j hj c, ⟨c - π j (p j hj c), ?_⟩⟩, ?_, ?_⟩, hdec j hj c⟩
    · change p j hj (c - π j (p j hj c)) = 0
      rw [map_sub, hpx, sub_self]
    · simp
    · rintro a ha
      have h1 := hdec j hj c a ha
      ext
      · exact h1
      · change (a.2 : F.obj (op j)) = c - π j (p j hj c)
        rw [← h1, ha]
        exact (add_sub_cancel_left _ _).symm
  · have hmap : F.map (homOfLE hjk).op ≫ p j hj = p k (hj.trans hjk) := by
      simp only [p]
      rw [← Category.assoc, hcomp]
    refine ⟨hmap, hπle j k hjk, fun z ↦ ?_, fun x z ↦ ?_⟩
    · change p j hj (F.map (homOfLE hjk).op (z : F.obj (op k))) = 0
      rw [← ConcreteCategory.comp_apply, hmap]
      exact z.2
    · rw [map_add, ← ConcreteCategory.comp_apply, hπle]
  · obtain ⟨k, hik, hjk, hk⟩ := hfactor j
    refine ⟨k, hjk, fun z ↦ ?_⟩
    have hz : p k (hj.trans hjk) (z : F.obj (op k)) = 0 := z.2
    rw [hk]
    change π j (p k (hj.trans hjk) (z : F.obj (op k))) = 0
    rw [hz, map_zero]

end CategoryTheory.Functor
