/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.RingTheory.HopfActionModuleData
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic

import WeilConjectures.AlgebraicGeometry.HopfCoactionLinearization

/-! # Integer weights of a rational representation of the multiplicative group

Source: Milne, Algebraic Groups (2017), Definition 12.11, Theorem 12.12 and
Remark 12.13, printed pp.234--235 (blueprint: lem-sfb-gm-representation-weight-basis).

We use the equivalent right-coaction formulation in the node. The coordinate Hopf algebra
is the canonical Laurent Hopf algebra used by `StandardGroupSchemes.multiplicative`.
The point value on a vector is obtained by evaluating its coaction at the given unit;
it is precisely the action on that vector tensored with 1, over every test algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry.GmRepresentation

/-- The integer-weight subspace, defined by c(v) = v tensor t^a, as an equalizer of
linear maps. Source: Milne, Theorem 12.12(d) and Remark 12.13, pp.234--235
(blueprint: lem-sfb-gm-representation-weight-basis). -/
def weightSpace {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (c : V →ₗ[k] V ⊗[k] LaurentPolynomial k) (a : ℤ) : Submodule k V :=
  LinearMap.eqLocus c
    ((TensorProduct.mk k V (LaurentPolynomial k)).flip (LaurentPolynomial.T a))

/-- Evaluation of a coaction at z on a vector: this is rho_R(z)(v tensor 1).
It is defined by the actual map 1 tensor ev_z, with no choice of point action.
Source: Milne, Remark 4.1, p.84, and Definition 12.11, p.234
(blueprint: lem-sfb-gm-representation-weight-basis). -/
def pointValue {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (c : V →ₗ[k] V ⊗[k] LaurentPolynomial k)
    (R : Type w) [CommRing R] [Algebra k R] (z : Rˣ) : V →ₗ[k] V ⊗[k] R :=
  (LaurentPolynomial.leval k z).lTensor V ∘ₗ c

/-- Every finite-dimensional rational G_m-representation has an internal integer-weight
decomposition with finite support and an ordered weight basis, valid on every test algebra.
Source: Milne, Definition 12.11, Theorem 12.12(a)--(d) and Remark 12.13, pp.234--235
(blueprint: lem-sfb-gm-representation-weight-basis).

Proof, following the seven steps of the node:
1. Use lem-sfb-hopf-coaction-linearization with E = k and its trivial action to identify
   representations with counital, coassociative Laurent coactions. Evaluation at a unit z
   pulls the universal linearization back to rho_R(z); its value on v tensor 1 is pointValue.
2. Use the unique finite Laurent expansion (def-weil-laurent-polynomial-ring) and the tensor
   universal property (def-weil-pbc-module-tensor-product) to extract linear coefficients
   p_a(v), with c(v) = sum_a p_a(v) tensor t^a and finite support for each v.
3. Coassociativity and Delta(t^a) = t^a tensor t^a show that c(p_a(v)) = p_a(v) tensor t^a.
   The counit identity then gives v = sum_a p_a(v).
4. On weight a, p_b is delta_ab times the identity. Applying p_b to a finite relation proves
   directness; the previous step proves that the canonical addition map is surjective.
5. Choose a finite spanning family (def-weil-finite-dimensional-subspace). The union of its
   coefficient supports is finite, and outside it every p_a vanishes, hence so does V_a.
6. The homogeneous components of that spanning family span V. Retain successive vectors
   outside the span of earlier ones to obtain a homogeneous ordered basis
   (def-weil-pbc-free-module); over a field (def-weil-field) this is independent and spanning.
   For V = 0 the retained list is empty.
7. Evaluate c(e_i) = e_i tensor t^(a_i) at z to obtain e_i tensor z^(a_i). The scalar
   extension of the basis is an R-basis by extending its coordinate maps, including for
   R = 0 and the empty basis. Negative exponents are defined on the unit z.
-/
theorem weightDecomposition_and_basis
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (c : V →ₗ[k] V ⊗[k] LaurentPolynomial k)
    (hcoassoc : HopfAction.Coassociative k (LaurentPolynomial k) V c)
    (hcounit : HopfAction.Counital k (LaurentPolynomial k) V c) :
    DirectSum.IsInternal (weightSpace c) ∧
      {a : ℤ | weightSpace c a ≠ ⊥}.Finite ∧
      ∃ (s : ℕ) (e : Module.Basis (Fin s) k V) (a : Fin s → ℤ),
        (∀ i : Fin s, c (e i) = e i ⊗ₜ[k] LaurentPolynomial.T (a i)) ∧
        ∀ (R : Type (max u w)) [CommRing R] [Algebra k R] (z : Rˣ) (i : Fin s),
          pointValue c R z (e i) = e i ⊗ₜ[k] ((z ^ a i : Rˣ) : R) := by
  sorry

end AlgebraicGeometry.GmRepresentation
