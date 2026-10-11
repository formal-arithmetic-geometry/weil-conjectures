/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie

/-!
# Tangent matrices and the differential of a rational representation

Source: Milne, Algebraic Groups (2017), Chapter 10, Lie algebra of a closed matrix subgroup
and differential of a representation (blueprint: lem-wf-lie-algebra-derivation-bracket).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralLinearGroup

/-- The matrices `X` for which `1 + εX` belongs to a closed matrix subgroup form a linear
subspace closed under commutators. Every rational representation has a linear differential
on this subspace, characterized by its dual-number points, preserving the commutator.
Source: Milne, Algebraic Groups (2017), Chapter 10
(blueprint: lem-wf-lie-algebra-derivation-bracket).

Proof: (1) Zero is tangent since the identity is a group point. Multiplication of dual-number
points gives `1 + ε(X + Y)`, and naturality under `ε ↦ aε` gives scalar closure.
(2) By lem-wf-mixed-commutator-tangent, the two-parameter commutator has mixed coefficient
`XY - YX`, which is tangent. (3) The associative matrix commutator is bilinear, alternating
and satisfies Jacobi, so this is a Lie subalgebra in the sense of def-wf-lie-algebra.
(4) A rational representation (def-wf-algebraic-representations) is natural in the test
algebra and respects multiplication. Thus its ε-coefficient is additive and homogeneous.
Apply naturality to the two inclusions of the dual numbers into `k[ε, δ]/(ε², δ²)`.
The representation takes the mixed commutator to the mixed commutator of the images.
Naturality under `η ↦ εδ` and comparison of mixed coefficients prove preservation of
`XY - YX`, again using lem-wf-mixed-commutator-tangent (also for the target general linear
group). (5) This is precisely the Lie-representation identity of def-wf-lie-algebra.

Finite-dimensional vector spaces are written in coordinates `kⁿ` and `kᵐ`; neither index
set is required to be nonempty. The final equality uses any `Z` representing `[X,Y]` in the
subspace, avoiding a file-local choice of Lie-ring instance. -/
theorem exists_tangentMatrixSubmodule_differential
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (I : Ideal (Matrix.GeneralLinearGroup.CoordinateRing n k)) [I.IsHopfIdeal k] :
    ∃ S : Submodule k (Matrix n n k),
      (∀ X : Matrix n n k, X ∈ S ↔
        dualUnit X ∈ Matrix.GeneralLinearGroup.zeroLocus I (DualNumber k)) ∧
      (∀ X ∈ S, ∀ Y ∈ S, X * Y - Y * X ∈ S) ∧
      (∀ (r : RationalHom (subgroupScheme I) m) [IsMonHom r],
        ∃ d : S →ₗ[k] Matrix m m k,
          (∀ (X : S) (g : AlgebraicGeometry.points (subgroupScheme I) (DualNumber k)),
            homMulEquiv n k (DualNumber k) (g ≫ subgroupSchemeι I) = dualUnit X.val →
              r.points (DualNumber k) g = dualUnit (d X)) ∧
          (∀ X Y Z : S, Z.val = X.val * Y.val - Y.val * X.val →
            d Z = d X * d Y - d Y * d X)) := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
