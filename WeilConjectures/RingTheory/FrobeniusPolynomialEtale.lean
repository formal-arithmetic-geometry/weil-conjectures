/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Algebra.CharP.Lemmas

/-!
# Étaleness of the Frobenius polynomial solution algebra

The solution algebra `R[X₁, …, Xₙ] ⧸ (b_i + X_i - ∑ⱼ a_ij X_j^p)` of a Frobenius-semilinear
inhomogeneous system in characteristic `p` is étale.

## Implementation details

The presentation pairs each relation with its variable. Derivatives of `p`th powers vanish in
characteristic `p`, so the Jacobian matrix is the identity and the presentation is submersive;
this also covers the empty system.

## References

* [Stacks, Tag 0GKU] (proof)
-/

@[expose] public section

set_option autoImplicit false

universe u

open MvPolynomial

namespace Algebra

/-- The solution algebra for a Frobenius-semilinear inhomogeneous system is étale.
-/
theorem frobenius_polynomial_etale
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (n : ℕ) (a : Fin n → Fin n → R) (b : Fin n → R) :
    Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range
      (fun i : Fin n ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p))) := by
  classical
  let r : Fin n → MvPolynomial (Fin n) R :=
    fun i ↦ C (b i) + X i - ∑ j, C (a i j) * X j ^ p
  let P : PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range r)) (Fin n) (Fin n) :=
    { Presentation.naive (v := r) with map := _root_.id, map_inj := Function.injective_id }
  have hderiv (i j : Fin n) : pderiv i (r j) = if i = j then 1 else 0 := by
    simp [r, map_sub, map_add, map_sum, Pi.single_apply, eq_comm]
  have hmatrix : P.jacobiMatrix = 1 := by
    ext i j : 1
    simpa [P, PreSubmersivePresentation.jacobiMatrix_apply, Matrix.one_apply,
      Pi.single_apply] using hderiv i j
  have hjac : P.jacobian = 1 := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmatrix, Matrix.det_one,
      map_one]
  exact (show SquareJacobianPresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range r)) (Fin n) from
    { P with jacobian_isUnit := by rw [hjac]; exact isUnit_one, map_eq_id := rfl }).etale

end Algebra
