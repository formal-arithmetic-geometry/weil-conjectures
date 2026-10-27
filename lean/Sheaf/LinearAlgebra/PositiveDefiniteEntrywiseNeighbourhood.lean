module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Entrywise neighbourhoods of positive definite real symmetric matrices

Source: agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`, motivated by Milne, *Abelian Varieties*,
II §1, Lemma 1.3, printed pp. 77–78
(blueprint: lem-sfb-positive-definite-entrywise-neighbourhood).
Milne supplies the surrounding rational-algebra setting, not this matrix lemma.
-/

@[expose] public section

namespace Matrix

/-- A positive definite real symmetric matrix admits a uniform positive entrywise
perturbation bound among symmetric matrices, including the empty matrix.

Source: agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`; Milne, *Abelian Varieties*, II §1,
Lemma 1.3, printed pp. 77–78 motivates only the surrounding rational-algebra setting
(blueprint: lem-sfb-positive-definite-entrywise-neighbourhood).

Proof plan:
1. If `n = 0`, take `ε = 1`; all vectors are zero, so positivity is vacuous.
2. Otherwise give `ℝⁿ` its standard inner product and let `T` be multiplication by `G`.
   Symmetry of `G` makes `T` symmetric. Apply the orthonormal eigenbasis theorem
   `LinearMap.IsSymmetric.eigenvectorBasis` and its eigenvector identity
   `LinearMap.IsSymmetric.apply_eigenvectorBasis`
   (node `lem-sfb-real-symmetric-orthonormal-eigenbasis`).
3. The quadratic form of `G` on each unit eigenvector is its eigenvalue, hence is
   positive. The minimum `c` of these finitely many eigenvalues is positive. Expanding
   in the orthonormal eigenbasis gives `q_G(z) ≥ c * ∑ a, z a ^ 2` for every `z`.
4. Take `ε = c / (2 * n)`. For `E = H - G`, put `S = ∑ a, z a ^ 2` and
   `L = ∑ a, |z a|`. Expanding the sum of `(|z a| - |z b|)^2` gives `L^2 ≤ n*S`.
   The entrywise bound and the triangle inequality give
   `|q_E(z)| ≤ ε * L^2 ≤ (c / 2) * S`. Since `q_H = q_G + q_E`, this yields
   `q_H(z) ≥ (c / 2) * S > 0` for every nonzero `z`. Together with the assumed
   symmetry of `H`, this is positive definiteness.
-/
theorem posDef_entrywise_neighbourhood (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : Matrix (Fin n) (Fin n) ℝ,
      H.IsSymm → (∀ a b : Fin n, |H a b - G a b| < ε) → H.PosDef := by
  sorry

end Matrix
