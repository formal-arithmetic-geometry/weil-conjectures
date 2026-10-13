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
      fun j hj ↦ F.map (homOfLE hj).op ≫ r
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
  sorry

end CategoryTheory.Functor
