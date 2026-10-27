module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Pi
import Sheaf.LinearAlgebra.RationalLinearSystemParametrization
import Sheaf.LinearAlgebra.PositiveDefiniteEntrywiseNeighbourhood
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Rational strict feasibility for symmetric matrix equations

Source: agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`, recorded in the DAG proof;
Milne, *Abelian Varieties*, II §1, Lemma 1.3, printed pp. 77–78 motivates only
its ambient rational algebra, and does not assert this matrix lemma
(blueprint: lem-sfb-rational-positive-definite-feasibility).
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

/-- The real extension of a rational linear map on symmetric matrices, in the basis
`Eᵢᵢ`, `Eᵢⱼ + Eⱼᵢ` for `i < j`. Over both fields `selfAdjoint` is exactly the space
of symmetric matrices. In the formula, `selfAdjointPart ℚ (single i j 1)` is `Eᵢᵢ`
when `i = j`, whereas `selfAdjointPart ℚ (single i j 2)` is `Eᵢⱼ + Eⱼᵢ` when `i < j`.
Thus each upper-triangular entry multiplies exactly the corresponding rational basis
image under `L`, included in the real coordinate space.

Source: the explicit coefficient convention in the agent auxiliary Gram-matrix argument,
motivated by Milne, *Abelian Varieties*, II §1, Lemma 1.3, printed pp. 77–78
(blueprint: lem-sfb-rational-positive-definite-feasibility). -/
noncomputable def rationalSymmetricRealExtension {n m : ℕ}
    (L : selfAdjoint (Matrix (Fin n) (Fin n) ℚ) →ₗ[ℚ] (Fin m → ℚ)) :
    selfAdjoint (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi fun k ↦
    ∑ i : Fin n, ∑ j : Fin n,
      (if i ≤ j then
        ((L (selfAdjointPart ℚ (single i j (if i = j then 1 else 2))) k : ℚ) : ℝ)
      else 0) •
        ((LinearMap.proj j).comp
          ((LinearMap.proj i).comp
            (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)).subtype))

/-- Real strict feasibility of rational symmetric matrix equations implies rational
strict feasibility, including empty matrices and empty coordinate spaces.

Source: agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`; Milne, *Abelian Varieties*, II §1,
Lemma 1.3, printed pp. 77–78 motivates the setting but does not assert this lemma
(blueprint: lem-sfb-rational-positive-definite-feasibility).

Proof:
1. For `n = 0`, the premise forces the real image of `b` to vanish; injectivity of
   rational inclusion gives `b = 0`. The empty rational matrix is vacuously positive
   definite. Otherwise identify symmetric matrices with their upper-triangular entries.
2. The columns `L(Eᵢᵢ)` and `L(Eᵢⱼ + Eⱼᵢ)` give a rational matrix `A` for `L` and
   the same real matrix for `rationalSymmetricRealExtension L`. Apply
   [lem-sfb-rational-linear-system-parametrization] to the given real solution.
   Lift the rational particular solution and homogeneous directions to symmetric
   matrices `H₀`, `Vⱼ`. Then `L(H₀) = b`, `L(Vⱼ) = 0` and
   `G = (H₀)ℝ + ∑ j, tⱼ (Vⱼ)ℝ` for real parameters `tⱼ`.
3. Apply [lem-sfb-positive-definite-entrywise-neighbourhood] at `G`, obtaining `ε > 0`.
   If there are no directions, return `H₀`. Otherwise put
   `B = 1 + ∑ j, ∑ a, ∑ b, |(Vⱼ)ℝ a b|` and `δ = ε / B > 0`.
4. By [lem-sfb-real-rational-interval-density], choose rational `qⱼ` with
   `|qⱼ - tⱼ| < δ`. Set `H = H₀ + ∑ j, qⱼ Vⱼ`. It is symmetric and rational,
   and linearity gives the exact equality `L(H) = b`.
5. Each entry of `Hℝ - G` is bounded by
   `∑ j, |qⱼ - tⱼ| |(Vⱼ)ℝ a b| ≤ δ (B - 1) < ε`.
   The neighbourhood theorem therefore makes `Hℝ` positive definite.
-/
theorem exists_rat_posDef_of_real_solution {n m : ℕ}
    (L : selfAdjoint (Matrix (Fin n) (Fin n) ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (b : Fin m → ℚ)
    (h : ∃ G : selfAdjoint (Matrix (Fin n) (Fin n) ℝ),
      (G : Matrix (Fin n) (Fin n) ℝ).PosDef ∧
        rationalSymmetricRealExtension L G = (fun k ↦ (b k : ℝ))) :
    ∃ H : selfAdjoint (Matrix (Fin n) (Fin n) ℚ),
      L H = b ∧ ((H : Matrix (Fin n) (Fin n) ℚ).map (fun q : ℚ ↦ (q : ℝ))).PosDef := by
  sorry

end Matrix
