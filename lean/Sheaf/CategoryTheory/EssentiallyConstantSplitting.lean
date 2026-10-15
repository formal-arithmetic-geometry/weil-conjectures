/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
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

-- In the unchanged statement, the lambda index defining `p` is used only implicitly.
set_option linter.unusedVariables.funArgs false in
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
  let cone : (Functor.const ℕᵒᵖ).obj X ⟶ F :=
    NatTrans.ofOpSequence π (fun n ↦ by simpa using (hπ n).symm)
  have hcone (j k : ℕ) (hjk : j ≤ k) :
      π k ≫ F.map (homOfLE hjk).op = π j := by
    simpa [cone] using (cone.naturality (homOfLE hjk).op).symm
  let p : ∀ j : ℕ, i₀ ≤ j → (F.obj (op j) ⟶ X) :=
    fun j hj ↦ F.map (homOfLE hj).op ≫ r
  let Z : ∀ j : ℕ, i₀ ≤ j → AddSubgroup (F.obj (op j)) :=
    fun j hj ↦ (p j hj).hom.ker
  have hsplit (j : ℕ) (hj : i₀ ≤ j) : π j ≫ p j hj = 𝟙 X := by
    dsimp only [p]
    rw [← Category.assoc, hcone, hr]
  have hsplit_apply (j : ℕ) (hj : i₀ ≤ j) (x : X) : p j hj (π j x) = x := by
    exact congrArg (fun f : X ⟶ X ↦ f x) (hsplit j hj)
  have hp (j k : ℕ) (hj : i₀ ≤ j) (hjk : j ≤ k) :
      F.map (homOfLE hjk).op ≫ p j hj = p k (hj.trans hjk) := by
    dsimp only [p]
    rw [← Category.assoc, ← F.map_comp]
    rfl
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    refine ⟨hsplit j hj, ?_, ?_⟩
    · intro x y hxy
      simpa only [hsplit_apply] using congrArg (p j hj) hxy
    · intro c
      have first (a : X × Z j hj)
          (ha : c = π j a.1 + (a.2 : F.obj (op j))) : a.1 = p j hj c := by
        have hz : p j hj (a.2 : F.obj (op j)) = 0 := a.2.property
        have hc := congrArg (p j hj) ha
        simpa only [map_add, hsplit_apply, hz, add_zero] using hc.symm
      refine ⟨?_, first⟩
      let z : Z j hj := ⟨c - π j (p j hj c), by
        change p j hj (c - π j (p j hj c)) = 0
        rw [map_sub, hsplit_apply, sub_self]⟩
      refine ⟨⟨p j hj c, z⟩, ?_, ?_⟩
      · change c = π j (p j hj c) + (c - π j (p j hj c))
        simp only [← add_sub_assoc, add_sub_cancel_left]
      · intro a ha
        apply Prod.ext (first a ha)
        apply Subtype.ext
        have ha' : c = π j (p j hj c) + (a.2 : F.obj (op j)) := by
          simpa only [first a ha] using ha
        change (a.2 : F.obj (op j)) = c - π j (p j hj c)
        calc
          (a.2 : F.obj (op j)) =
              (π j (p j hj c) + (a.2 : F.obj (op j))) - π j (p j hj c) :=
            (add_sub_cancel_left _ _).symm
          _ = c - π j (p j hj c) := congrArg (fun d ↦ d - π j (p j hj c)) ha'.symm
  · intro j k hj hjk
    refine ⟨hp j k hj hjk, hcone j k hjk, ?_, ?_⟩
    · intro z
      change p j hj (F.map (homOfLE hjk).op (z : F.obj (op k))) = 0
      have hz : p k (hj.trans hjk) (z : F.obj (op k)) = 0 := z.property
      have heq := congrArg
        (fun f : F.obj (op k) ⟶ X ↦ f (z : F.obj (op k))) (hp j k hj hjk)
      exact heq.trans hz
    · intro x z
      rw [map_add]
      have heq := congrArg (fun f : X ⟶ F.obj (op j) ↦ f x) (hcone j k hjk)
      exact congrArg (fun a ↦ a + F.map (homOfLE hjk).op (z : F.obj (op k))) heq
  · intro j hj
    obtain ⟨k, hik, hjk, hk⟩ := hfactor j
    refine ⟨k, hjk, ?_⟩
    intro z
    have hz : p k (hj.trans hjk) (z : F.obj (op k)) = 0 := z.property
    rw [hk]
    change π j (p k (hj.trans hjk) (z : F.obj (op k))) = 0
    rw [hz, map_zero]

end CategoryTheory.Functor
