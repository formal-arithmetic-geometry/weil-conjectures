/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

/-!
# Rational affine parametrization of a real-solvable rational linear system

Source: the agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`, recorded in the DAG proof;
Milne, *Abelian Varieties*, II §1, Lemma 1.3, printed pp.77–78 provides context only
(blueprint: lem-sfb-rational-linear-system-parametrization).
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

/-- A rational system with a real solution has a rational particular solution and finitely
many rational homogeneous directions parametrizing every real solution. Zero dimensions
and an empty family of directions are allowed.

Source: the agent auxiliary to the Gram-matrix argument for
`lem-sfb-split-real-algebra-positive-squares`; Milne, *Abelian Varieties*, II §1,
Lemma 1.3, printed pp.77–78 supplies the rational-algebra context, not this assertion
(blueprint: lem-sfb-rational-linear-system-parametrization).

Proof: Induct on the number of columns d, simultaneously for every number of rows m.
1. For d = 0, real consistency and injectivity of the rational inclusion give b = 0.
Take the empty vector and k = 0. If A = 0 for any d, consistency again gives b = 0;
take x₀ = 0 and the d coordinate vectors. They span every real vector, also when m = 0.
2. Otherwise choose a nonzero entry and move it to position (1,1) by row and column
permutations. Row permutations reorder equations; a column permutation sends the new
unknown z to the old unknown Pz, so undo it on the particular solution and all directions.
Write an unknown as (u,z), put α = b₁/a₁₁ and rₐ = a₁,ₐ₊₁/a₁₁. The first equation is
u = α - ∑ₐ rₐ zₐ.
3. For the remaining rows put Cᵢ₋₁,ₐ = aᵢ,ₐ₊₁ - aᵢ₁ rₐ and eᵢ₋₁ = bᵢ - aᵢ₁ α.
Substitution makes the other equations precisely Cz = e, over both ℚ and ℝ. All
coefficients are rational and the pivot remains nonzero in ℝ, so its inverse also casts
correctly. The real solution therefore gives real consistency of the reduced system.
4. Apply induction to its d - 1 columns and m - 1 rows, obtaining z₀ and directions wⱼ.
Set x₀ = (α - ∑ₐ rₐ (z₀)ₐ, z₀) and vⱼ = (-∑ₐ rₐ (wⱼ)ₐ, wⱼ). Substitution proves
Ax₀ = b. The first row of Avⱼ cancels and every remaining row is a row of Cwⱼ = 0.
5. Any real solution (u,z) gives a reduced solution. Write z = (z₀)ℝ + ∑ⱼ tⱼ (wⱼ)ℝ
by induction and substitute into u = αℝ - ∑ₐ (rₐ)ℝ zₐ. Distributing the finite sums
gives the first coordinate of (x₀)ℝ + ∑ⱼ tⱼ (vⱼ)ℝ; the other coordinates already agree.
Undo the column permutation. This includes d = 1, m = 1 and k = 0. -/
theorem exists_rat_affine_parametrization_of_real_solution
    {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (h : ∃ x : Fin d → ℝ,
      (A.map (fun q : ℚ ↦ (q : ℝ))).mulVec x = (fun i ↦ (b i : ℝ))) :
    ∃ (k : ℕ) (x₀ : Fin d → ℚ) (v : Fin k → Fin d → ℚ),
      A.mulVec x₀ = b ∧
      (∀ j : Fin k, A.mulVec (v j) = 0) ∧
      ∀ x : Fin d → ℝ,
        (A.map (fun q : ℚ ↦ (q : ℝ))).mulVec x = (fun i ↦ (b i : ℝ)) →
        ∃ t : Fin k → ℝ,
          x = (fun a ↦ (x₀ a : ℝ)) + ∑ j : Fin k, t j • (fun a ↦ (v j a : ℝ)) := by
  sorry

end Matrix
