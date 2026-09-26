/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import WeilConjectures.AlgebraicGeometry.GroupScheme.MatrixGroup

/-!
# Tangent spaces of matrix groups and the group–Lie comparison

For a Zariski-closed subset `s` of the space of matrices and a point `a` of it, the tangent space
`T_a s` is cut out inside the space of matrices by the differentials at `a` of the polynomials
vanishing on `s`; equivalently `X ∈ T_a s` when `a + εX` is an `s`-point over the dual numbers
`k[ε]/(ε²)`.  The Lie algebra of a matrix algebraic group is `Lie G = T_1 G`, with bracket
`⁅X, Y⁆ = XY - YX` coming from the associative matrix product.

Smoothness of a finite-type matrix group scheme — that the tangent space has the dimension of the
local ring — is Cartier's theorem, stated scheme-theoretically in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier`.

## Main declarations

* `Matrix.polyDifferential`: the differential at a point of a polynomial in the matrix entries.
* `Matrix.tangentSpace`: the tangent space of a subset of matrix space at a point.
* `Subgroup.lieAlgebra`: the Lie algebra `Lie G = T_1 G` of a subgroup of `GL n k`.
* `Matrix.invariant_iff_lieAlgebra_invariant_and_mem_lieAlgebra_center`: the group–Lie comparison.
-/

@[expose] public section

open scoped Matrix Matrix.Zariski

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Blueprint `sk-d-tangent`: Tangent spaces and rational actions.  The differential at `a` of a
polynomial function of the matrix entries: the linear form `X ↦ ∑ (∂f/∂x_{ij})(a) * X i j`. -/
noncomputable def polyDifferential (f : MvPolynomial (n × n) k) (a : Matrix n n k) :
    Matrix n n k →ₗ[k] k :=
  ∑ p : n × n, MvPolynomial.eval (fun q ↦ a q.1 q.2) (MvPolynomial.pderiv p f) •
    Matrix.entryLinearMap k k p.1 p.2

/-- Blueprint `sk-d-tangent`: Tangent spaces and rational actions.  The tangent space at `a` of a
subset `s` of matrix space: the matrices `X` killed by the differentials at `a` of all the
polynomials vanishing on `s`, equivalently those with `a + εX` an `s`-point over the dual
numbers. -/
noncomputable def tangentSpace (s : Set (Matrix n n k)) (a : Matrix n n k) :
    Submodule k (Matrix n n k) :=
  ⨅ f ∈ MvPolynomial.vanishingIdeal (k := k)
      ((fun (M : Matrix n n k) (p : n × n) ↦ M p.1 p.2) '' s),
    LinearMap.ker (polyDifferential f a)

end Matrix

namespace Subgroup

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Blueprint `sk-d-tangent`: Tangent spaces and rational actions.  The Lie algebra `Lie G = T_1 G`
of a subgroup of `GL n k`, with the commutator bracket `⁅X, Y⁆ = XY - YX`.  That the tangent space
is closed under the bracket is part of the proposition `sk-i-restriction`. -/
noncomputable def lieAlgebra (G : Subgroup (GL n k)) : LieSubalgebra k (Matrix n n k) where
  __ := Matrix.tangentSpace (Units.val '' (G : Set (GL n k))) 1
  lie_mem' := by sorry

end Subgroup

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]

/-- Blueprint `sk-p-comparison`: Group–Lie comparison.  For a connected matrix algebraic group `G`
a subspace of the defining representation is `G`-invariant if and only if it is invariant under
`Lie G`, and `Lie (Z(G)°)` is the centre of `Lie G`.  A general rational representation
`r : G → GL M` reduces to this statement for the image `r(G)`, a closed connected subgroup of
`GL M` by `sk-p-geometry`. -/
theorem invariant_iff_lieAlgebra_invariant_and_mem_lieAlgebra_center
    (G : Subgroup (GL n k)) (hG : IsClosed (G : Set (GL n k)))
    (hGconn : IsPreconnected (G : Set (GL n k))) :
    (∀ U : Submodule k (n → k),
        (∀ g ∈ G, ∀ v ∈ U, (g : Matrix n n k) *ᵥ v ∈ U) ↔
          (∀ X ∈ G.lieAlgebra, ∀ v ∈ U, X *ᵥ v ∈ U)) ∧
      (∀ X : Matrix n n k,
        X ∈ (G.centerOf.identityComponent).lieAlgebra ↔
          X ∈ G.lieAlgebra ∧ ∀ Y ∈ G.lieAlgebra, ⁅X, Y⁆ = 0) := by
  sorry

end Matrix
