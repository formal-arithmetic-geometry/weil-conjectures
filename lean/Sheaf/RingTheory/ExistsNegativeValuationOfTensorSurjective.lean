/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor surjectivity detects a negative discrete valuation

Source: Stacks Project, Varieties, Lemma 09N5, induction base case
(blueprint: lem-sc-dvr-tensor-surjective-negative-valuation).
-/

universe u

namespace IsDiscreteValuationRing

/-- Source: Stacks Project, Varieties, Lemma 09N5, induction base case
(blueprint: lem-sc-dvr-tensor-surjective-negative-valuation).
The tensor product is over `ℤ`, and its canonical map sends `a ⊗ b` to `a * b` in `K`.
The normalized additive valuation is `-WithZero.log` of the maximal-ideal adic valuation:
a uniformizer has multiplicative value `WithZero.exp (-1)`, hence additive value `1`.

Proof: Choose a uniformizer `t` of `B`. Its inverse has additive valuation `-1` and is
not in `B` (lem-sc-dvr-valuation-ring-characterization). Tensor surjectivity expresses
`t⁻¹` as a finite sum of products `a_j * b_j`. If all nonzero elements of `A` had
nonnegative valuation, then every nonzero product would have nonnegative valuation
by lem-sc-dvr-valuation-arithmetic and lem-sc-dvr-valuation-ring-characterization.
By lem-sc-dvr-nonnegative-valuation-in-ring these products belong to `B`; zero products
also belong to `B`. Their sum belongs to `B`, a contradiction. Thus some nonzero
`a_j` has negative valuation. -/
theorem exists_negative_valuation_of_tensor_surjective {K : Type u} [Field K]
    (A B : Subring K) [IsFractionRing A K] [IsDiscreteValuationRing B]
    [IsFractionRing B K]
    (h : Function.Surjective
      (Algebra.TensorProduct.productMap A.subtype.toIntAlgHom B.subtype.toIntAlgHom)) :
    ∃ x : A, x ≠ 0 ∧ -WithZero.log ((maximalIdeal B).valuation K (x : K)) < 0 := by
  sorry

end IsDiscreteValuationRing
