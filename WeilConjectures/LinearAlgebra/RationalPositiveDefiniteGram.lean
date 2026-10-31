/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Rational positive definite matrices as sums of outer squares

Source: the agent auxiliary for the split-real sum-of-squares argument, motivated by
Milne, Abelian Varieties, II §1, proof of Lemma 1.3, printed pp. 77–78
(blueprint: lem-sfb-rational-positive-definite-gram). The matrix lemma is not asserted
in Milne; its proof is the rational orthogonal-basis argument recorded below.
-/

@[expose] public section

namespace Matrix

/-- A symmetric rational matrix that is positive definite over the reals is a finite
sum of outer squares of rational vectors, with equality of rational entries.

Source: the agent auxiliary for the split-real sum-of-squares argument, motivated by
Milne, Abelian Varieties, II §1, proof of Lemma 1.3, printed pp. 77–78
(blueprint: lem-sfb-rational-positive-definite-gram).

Proof: if `n = 0`, take `r = 0`. Otherwise apply
`LinearMap.BilinForm.exists_orthogonal_basis`
(lem-sfb-rational-symmetric-form-orthogonal-basis) to the symmetric rational bilinear
form `B(x,y) = ∑ i, ∑ j, x i * H i j * y j` on the coordinate vector space. For each
orthogonal basis vector `u k`, its nonzero rational coordinates remain nonzero over
ℝ. Real positive definiteness therefore gives `d k = B (u k) (u k) > 0`. Expand every
coordinate vector as `e i = ∑ k, c k i • u k`. Bilinearity and orthogonality give
`H i j = ∑ k, d k * c k i * c k j` over ℚ. Write each positive rational `d k` as
`a k / b k`, with positive integer numerator and denominator. It equals the sum of
`a k * b k` copies of `(1 / b k)^2`. For each `k`, repeat the rational vector with
coordinates `c k i / b k` exactly `a k * b k` times. Enumerate these finitely many
vectors by `Fin r`. Distributing the sums recovers the displayed rational entry
identity for every `i` and `j`. -/
theorem exists_sum_mul_self_of_rat_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : H.IsSymm) (hpos : (H.map (fun x : ℚ ↦ (x : ℝ))).PosDef) :
    ∃ (r : ℕ) (v : Fin r → Fin n → ℚ),
      ∀ i j : Fin n, H i j = ∑ k : Fin r, v k i * v k j := by
  sorry

end Matrix
