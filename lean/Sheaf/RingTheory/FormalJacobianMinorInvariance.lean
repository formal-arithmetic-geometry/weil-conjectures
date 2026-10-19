/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions
import Sheaf.RingTheory.FormalJacobianCoordinateChainRule

/-!
# Invariance of formal Jacobian minor ideals

Source: Stacks Project, Curves, Tag 0C4B, lemma-fitting-ideal-well-defined
(blueprint: lem-trf-formal-jacobian-minor-invariance).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace MvPowerSeries

/-- The ideal of fixed-size minors of the formal Jacobian modulo an ideal is independent
of its finite generating list and of regular parameter coordinates over the coefficient field.
Source: Stacks Project, Curves, Tag 0C4B, lemma-fitting-ideal-well-defined
(blueprint: lem-trf-formal-jacobian-minor-invariance).

Rows index generators and columns index variables. In the coordinate clause, `e` is the
field-algebra coordinate isomorphism sending the standard variables to `y`. Thus the derivative
of the same element `h` in the `y` coordinates is `e (pderiv F i (e.symm h))`.

Proof: For zero-size minors the ideal is the whole quotient, and for too many columns it
is zero. Write each new generator as a finite linear combination of the old ones.
The product rule gives J(g) = C J(f) modulo I. Apply Cauchy--Binet
[lem-weil-pbc-cauchy-binet] to every selected minor, obtaining containment of minor ideals;
the empty sum handles a generating list shorter than the minor size. Interchange the lists
for equality. For coordinates, the formal chain rule
[lem-trf-formal-jacobian-coordinate-chain-rule] gives J_x(f) = J_y(f) Q, where
Q = (partial y_k / partial x_i) is invertible. Reduce Q and its inverse modulo I, and apply
right-multiplication containment [lem-trf-fitting-ideal-minor-inclusions], clause (3), in both
directions. The empty matrices and zero-size and oversized minors are included throughout.
-/
theorem formalJacobian_minorIdeal_invariance (F : Type u) [Field F] (n s r : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) F))
    (hI : I ≤ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F)))
    (f : Fin s → MvPowerSeries (Fin n) F) (hf : Ideal.span (Set.range f) = I) :
    (∀ (l : ℕ) (g : Fin l → MvPowerSeries (Fin n) F), Ideal.span (Set.range g) = I →
      Matrix.minorIdeal s n r (fun j i ↦ Ideal.Quotient.mk I (pderiv F i (f j))) =
        Matrix.minorIdeal l n r (fun j i ↦ Ideal.Quotient.mk I (pderiv F i (g j)))) ∧
    (∀ (y : Fin n → MvPowerSeries (Fin n) F)
      (e : MvPowerSeries (Fin n) F ≃ₐ[F] MvPowerSeries (Fin n) F),
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn y) →
      (∀ i : Fin n, e (X i) = y i) →
      Matrix.minorIdeal s n r (fun j i ↦ Ideal.Quotient.mk I (pderiv F i (f j))) =
        Matrix.minorIdeal s n r
          (fun j i ↦ Ideal.Quotient.mk I (e (pderiv F i (e.symm (f j)))))) := by
  sorry

end MvPowerSeries
