/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.MatrixGroup

/-!
# Tangent spaces of matrix groups and the group–Lie comparison

For an ideal `I` of polynomials in the matrix entries and a point `a` of matrix space, the tangent
space `T_a I` is cut out inside the space of matrices by the differentials at `a` of the elements
of `I`; equivalently `X ∈ T_a I` when `a + εX` is a point of `I` over the dual numbers
`k[ε]/(ε²)`.  The tangent space is parameterised by an ideal rather than by a closed set because
the arguments of this block evaluate on nonreduced rings — the proof of the Lie inclusion works
over `k[ε, δ]/(ε², δ²)` — and because reducedness is a *theorem* here (Cartier's theorem,
`AlgebraicGeometry.isReduced_of_grpObj`), not something a definition should presuppose.  The
tangent space of a *set* is the case of its vanishing ideal.

The Lie algebra of a matrix algebraic group is `Lie G = T_1 G`, with bracket `⁅X, Y⁆ = XY - YX`
coming from the associative matrix product.

Smoothness of a finite-type matrix group scheme — that the tangent space has the dimension of the
local ring — is Cartier's theorem, stated scheme-theoretically in
`WeilConjectures.Mathlib.AlgebraicGeometry.Group.Smooth`.

The group–Lie comparison below is stated for the defining representation.  A general rational
representation `r : G → GL M` is meant to reduce to it by applying it to the image `r(G)`, a
closed connected subgroup of `GL M` by `sk-p-geometry`; that reduction additionally needs the
surjectivity of the differential `dr` of `r` onto `Lie (r(G))`, which is where characteristic
zero enters and which is not stated here.

## Main declarations

* `Matrix.polyDifferential`: the differential at a point of a polynomial in the matrix entries.
* `Matrix.tangentSpace`: the tangent space at a point of the zero locus of an ideal.
* `Matrix.tangentSpaceOfSet`: the tangent space at a point of a subset of matrix space.
* `Subgroup.lieAlgebra`: the Lie algebra `Lie G = T_1 G` of a subgroup of `GL n k`.
* `Matrix.invariant_iff_lieAlgebra_invariant`,
  `Matrix.coe_lieAlgebra_centerOf_identityComponent`: the group–Lie comparison.

## Blueprint

`Matrix.polyDifferential`, `Matrix.tangentSpace`, `Matrix.tangentSpaceOfSet` and
`Subgroup.lieAlgebra` implement `sk-d-tangent`. The closure of the tangent space under the
bracket and the group–Lie comparison theorems of this file are superseded, for closed subgroup
schemes of `GL_n`, by `Matrix.GeneralLinearGroup.dualUnit_bracket_mem`,
`Matrix.GeneralLinearGroup.invariant_iff_differential_invariant` and
`Matrix.GeneralLinearGroup.lieAlgebra_center`, which carry the blueprint labels.
-/

@[expose] public section

open scoped Matrix Zariski

-- `LieRing.ofAssociativeRing` is the commutator bracket of the matrix ring.  It is given a high
-- priority so that it wins over the `LieRing` structures that `Mathlib.Algebra.Lie.Matrix` puts
-- on `Matrix n n k` through its `LieAlgebra` and `Module` instances.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

namespace Matrix

/-- The differential at `a` of a polynomial function of the matrix entries: the linear form
`X ↦ ∑ (∂f/∂x_{ij})(a) * X i j`.
(blueprint: `sk-d-tangent`) -/
noncomputable def polyDifferential (f : MvPolynomial (n × n) k) (a : Matrix n n k) :
    Matrix n n k →ₗ[k] k :=
  ∑ p : n × n, MvPolynomial.eval (fun q ↦ a q.1 q.2) (MvPolynomial.pderiv p f) •
    Matrix.entryLinearMap k k p.1 p.2

/-- The tangent space at `a` of the zero locus of an ideal `I` of polynomials in the matrix
entries: the matrices `X` killed by the differentials at `a` of all the elements of `I`,
equivalently those with `a + εX` a point of `I` over the dual numbers.
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentSpace (I : Ideal (MvPolynomial (n × n) k)) (a : Matrix n n k) :
    Submodule k (Matrix n n k) :=
  ⨅ f ∈ I, LinearMap.ker (polyDifferential f a)

/-- The tangent space at `a` of a subset `s` of matrix space: the tangent space of the ideal of
polynomials vanishing on `s`.
(blueprint: `sk-d-tangent`) -/
noncomputable def tangentSpaceOfSet (s : Set (Matrix n n k)) (a : Matrix n n k) :
    Submodule k (Matrix n n k) :=
  tangentSpace (MvPolynomial.vanishingIdeal (k := k)
    ((fun (M : Matrix n n k) (p : n × n) ↦ M p.1 p.2) '' s)) a

end Matrix

namespace Subgroup

variable (G : Subgroup (GL n k))

/-- The tangent space at `1` of a subgroup of `GL n k` is closed under the commutator bracket. -/
theorem lie_mem_tangentSpaceOfSet_one {X Y : Matrix n n k}
    (hX : X ∈ Matrix.tangentSpaceOfSet (Units.val '' (G : Set (GL n k))) 1)
    (hY : Y ∈ Matrix.tangentSpaceOfSet (Units.val '' (G : Set (GL n k))) 1) :
    ⁅X, Y⁆ ∈ Matrix.tangentSpaceOfSet (Units.val '' (G : Set (GL n k))) 1 := by
  sorry

/-- The Lie algebra `Lie G = T_1 G` of a subgroup of `GL n k`, with the commutator bracket
`⁅X, Y⁆ = XY - YX`.
(blueprint: `sk-d-tangent`) -/
noncomputable def lieAlgebra : LieSubalgebra k (Matrix n n k) where
  __ := Matrix.tangentSpaceOfSet (Units.val '' (G : Set (GL n k))) 1
  lie_mem' := G.lie_mem_tangentSpaceOfSet_one

@[simp]
theorem coe_lieAlgebra :
    (G.lieAlgebra : Set (Matrix n n k)) =
      Matrix.tangentSpaceOfSet (Units.val '' (G : Set (GL n k))) 1 :=
  rfl

end Subgroup

namespace Matrix

variable [IsAlgClosed k] [CharZero k] (G : Subgroup (GL n k))

/-- For a connected matrix algebraic group `G` a subspace of the defining representation is
`G`-invariant if and only if it is invariant under `Lie G`. -/
theorem invariant_iff_lieAlgebra_invariant (hG : IsClosed (G : Set (GL n k)))
    (hGconn : IsPreconnected (G : Set (GL n k))) (U : Submodule k (n → k)) :
    (∀ g ∈ G, ∀ v ∈ U, (g : Matrix n n k) *ᵥ v ∈ U) ↔
      ∀ X ∈ G.lieAlgebra, ∀ v ∈ U, X *ᵥ v ∈ U := by
  sorry

/-- For a connected matrix algebraic group `G` the Lie algebra of the identity component of the
centre of `G` is the centre of `Lie G`. -/
theorem coe_lieAlgebra_centerOf_identityComponent (hG : IsClosed (G : Set (GL n k)))
    (hGconn : IsPreconnected (G : Set (GL n k))) :
    (G.centerOf.identityComponent.lieAlgebra : Set (Matrix n n k)) =
      {X ∈ (G.lieAlgebra : Set (Matrix n n k)) | ∀ Y ∈ G.lieAlgebra, ⁅X, Y⁆ = 0} := by
  sorry

end Matrix
