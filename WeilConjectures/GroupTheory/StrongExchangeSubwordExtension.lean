/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# One-letter extension of a reduced subword under strong exchange

Source: Björner--Brenti, *Combinatorics of Coxeter Groups*, Lemma 2.2.1,
printed pages 33--34, with the explicit exchange assumptions of the DAG node.
(blueprint: lem-sfb-exchange-reduced-subword-extension)
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace Subgroup

/-- A proper reduced subword of a reduced word admits a reduced one-position extension.
The `IsLeast` condition specifies the length function, including existence of words for
every group element. Positions use `Fin b.length`, with position `i` corresponding to
position `i + 1` in the source. Sorting a finite set of positions preserves the word order.

Source: Björner--Brenti, *Combinatorics of Coxeter Groups*, Lemma 2.2.1,
printed pages 33--34; the node's proof uses only its stated right strong exchange property.

Proof: Among the reduced selections representing `u`, minimize the largest omitted position
`r`. It exists since the full product differs from `u`. Every position after `r` is selected.
Write the selected product as `AB`, with `B` the full suffix after `r`, and the full product
as `P b_r B`. The conjugate `t = B⁻¹ b_r B` belongs to the specified conjugate set and
inserting `r` gives `ut = A b_r B`, represented by `length u + 1` letters. If this word
were not reduced, its length would be at most `length u`. Strong exchange deletes a
selected position `p`, and also implies that the selected word is nonempty. If `p > r`,
cancellation gives the full product with positions `r` and `p` removed, contradicting its
reducedness. If `p < r`, cancellation and `b_r² = 1` show that replacing `p` by `r` still
represents `u` with `length u` letters. All omitted positions are then below `r`, contrary
to the minimizing choice. Thus the inserted word is reduced. The selection sizes are
`length u` and `length u + 1`. For an empty selected word strong exchange already gives
a contradiction to a nonreduced insertion. An empty full word forces `u = v`; empty
generators allow only that empty word, so neither case satisfies the hypotheses.
(blueprint: lem-sfb-exchange-reduced-subword-extension) -/
theorem exists_reduced_subword_extension_of_strong_exchange
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (G : Subgroup (LinearMap.GeneralLinearGroup ℝ V)) (S : Set G)
    (hS : ∀ s ∈ S, s ≠ 1 ∧ s ^ 2 = 1)
    (ℓ : G → ℕ)
    (hlength : ∀ g : G, IsLeast
      {n : ℕ | ∃ a : List S, (a.map Subtype.val).prod = g ∧ a.length = n} (ℓ g))
    (hexchange : ∀ (a : List S) (t : G),
      (∃ (h : G) (s : S), t = h⁻¹ * s.val * h) →
      ℓ ((a.map Subtype.val).prod * t) ≤ ℓ (a.map Subtype.val).prod →
      1 ≤ a.length ∧ ∃ j : Fin a.length,
        (a.map Subtype.val).prod * t = ((a.eraseIdx j.val).map Subtype.val).prod)
    (b : List S) (u v : G)
    (hv : (b.map Subtype.val).prod = v) (hb : ℓ v = b.length)
    (huv : u ≠ v)
    (hsub : ∃ a : List S, a.Sublist b ∧ (a.map Subtype.val).prod = u ∧ a.length = ℓ u) :
    ∃ (I : Finset (Fin b.length)) (r : Fin b.length), r ∉ I ∧
      ((I.sort (· ≤ ·)).map (fun i ↦ (b.get i).val)).prod = u ∧
      I.card = ℓ u ∧
      ℓ ((((insert r I).sort (· ≤ ·)).map (fun i ↦ (b.get i).val)).prod) =
        (insert r I).card ∧
      (insert r I).card = ℓ u + 1 := by
  sorry

end Subgroup
