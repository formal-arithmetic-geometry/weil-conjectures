module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin

/-! # Sign of a permutation on two increasingly ordered complementary blocks

Source: Stacks Project, Tag 07Z7, `lemma-ideals-generated-by-minors`, determinant-expansion
hint. The ordered-shuffle calculation is agent-supplied, not asserted verbatim by Stacks.
(blueprint: lem-trf-ordered-block-permutation-sign)
-/

@[expose] public section

open scoped BigOperators

namespace Equiv.Perm

/-- The sign of a permutation carrying `T` to `I` factors into the two induced block signs
and the parity of the sums of the one-based labels of `I` and `T`. The equations `hα` and
`hβ` specify the induced permutations using the canonical increasing enumerations.
The label of `i : Fin q` in the source's set `{1, …, q}` is `i.val + 1`.

Source: Stacks Project, Tag 07Z7, `lemma-ideals-generated-by-minors`, expansion hint;
agent-supplied ordered-shuffle argument.
(blueprint: lem-trf-ordered-block-permutation-sign)

Proof plan:
1. For each subset `A`, concatenate its increasing enumeration and that of its complement
   to obtain a permutation `ρ_A`. Bijectivity of `σ` and `hσ` give the complementary image
   equality. Thus `δ = ρ_I⁻¹ ∘ σ ∘ ρ_T` acts as `α` and `β` on the two consecutive blocks.
2. Apply `Equiv.Perm.sign_eq_prod_prod_Ioi`
   [lem-sfb-permutation-sign-inversion-product] to each shuffle. Increasing enumerations
   give no internal inversions. The element with one-based label `a_j` has `a_j - j`
   smaller complementary elements. Hence the shuffle sign is `(-1)^e_A`, where
   `e_A = sum A - s * (s + 1) / 2`. Relabelling by subtracting one preserves sign and order.
3. Apply the same ordered-pair product to `δ`, `α`, and `β`. Cross-block factors are one;
   within each block the factors are exactly those of its induced permutation. Therefore
   `sign δ = sign α * sign β`, including empty blocks.
4. The sign homomorphism [def-weil-pbc-matrix-determinant] and the factorization of `σ`
   give the product of the two shuffle signs and the two block signs. Their exponent is
   `sum I + sum T - s * (s + 1)`. Since `s * (s + 1)` is even, this has the asserted parity.
   When `s = 0` or `s = q`, the shuffles are identities and the empty block sign is one.
   When `q = 0`, all permutations are the identity of the empty set, with sign one.
-/
theorem sign_orderedBlocks {q s : ℕ} (hs : s ≤ q) (T I : Finset (Fin q))
    (hT : T.card = s) (hI : I.card = s) (σ : Equiv.Perm (Fin q))
    (hσ : T.image σ = I) (α : Equiv.Perm (Fin s)) (β : Equiv.Perm (Fin (q - s)))
    (hα : ∀ a : Fin s, σ (T.orderEmbOfFin hT a) = I.orderEmbOfFin hI (α a))
    (hβ : ∀ b : Fin (q - s),
      σ ((Tᶜ).orderEmbOfFin (by simp [Finset.card_compl, hT]) b) =
        (Iᶜ).orderEmbOfFin (by simp [Finset.card_compl, hI]) (β b)) :
    (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ ((∑ i ∈ I, (i.val + 1)) + ∑ t ∈ T, (t.val + 1)) *
        (Equiv.Perm.sign α : ℤ) * (Equiv.Perm.sign β : ℤ) := by
  sorry

end Equiv.Perm
