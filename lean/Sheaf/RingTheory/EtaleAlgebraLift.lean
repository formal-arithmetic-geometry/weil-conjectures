/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.JacobianPresentationLift
public import Mathlib.RingTheory.Etale.Basic

/-!
# Étale algebras lift across arbitrary quotients

Source: Stacks Project, Tag 04D1; the Weil conjectures blueprint, sec-smooth-purity,
sk-prop-sf-open-closed-triangle (blueprint: lem-exc-etale-algebra-lift).

## Main statements

- `Algebra.SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv`: the explicit
  lifted quotient is étale of finite presentation, and its specified reduction is an isomorphism.
- `Algebra.exists_etale_coefficientLift`: every étale quotient algebra admits such a lift.
-/

@[expose] public section

universe u v

namespace Algebra

/-- The lifted Jacobian quotient is étale of finite presentation, and the specified reduction
induces an isomorphism modulo the extended ideal. Source: Stacks Project, Tag 04D1; blueprint
node `lem-exc-etale-algebra-lift` (blueprint: lem-exc-etale-algebra-lift).

Proof:
1. Regard the lifted relations and `t * Δ - 1` as equations in the old variables and `t`.
   Their Jacobian matrix has upper-right block zero, upper-left block the original Jacobian,
   and bottom-right entry `Δ`, so its determinant is `Δ²`. Since `t * Δ = 1` in the quotient,
   this determinant is a unit. The square Jacobian criterion
   `lem-exc-etale-jacobian-presentation` gives étaleness and finite presentation.
2. Modulo the extended ideal, the coefficient lifts become the original relations. The
   original determinant is already a unit, so adjoining `t` with `t * Δ - 1 = 0` determines
   `t` uniquely as its inverse. The universal property of the quotient gives an isomorphism
   whose composite with the quotient map is precisely the specified `L.reduction` from
   `def-exc-etale-algebra-lift`. -/
theorem SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing ∧
      ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
        ∀ x : L.LiftRing,
          e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  sorry

/-- Every étale finite-presentation algebra over an arbitrary quotient admits the explicit
Jacobian lift and its reduction isomorphism. Source: Stacks Project, Tag 04D1; blueprint node
`lem-exc-etale-algebra-lift` (blueprint: lem-exc-etale-algebra-lift).

Proof:
1. By `lem-exc-etale-jacobian-presentation`, the given étale algebra admits a square Jacobian
   presentation. Reindex its finite variables and relations by `Fin m`.
2. Choose lifts of the coefficients of its finitely many relations along `A → A/I`, giving
   the data of `def-exc-etale-algebra-lift`.
3. Apply the determinant and reduction argument of
   `SquareJacobianPresentation.CoefficientLift.etale_and_reduction_equiv`. It gives the
   requested étale finite-presentation lift and the specified reduction isomorphism.
   No step uses nilpotence of the ideal. -/
theorem exists_etale_coefficientLift
    {A : Type u} [CommRing A] (I : Ideal A)
    (B : Type v) [CommRing B] [Algebra (A ⧸ I) B] [Algebra.Etale (A ⧸ I) B] :
    ∃ (m : ℕ) (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
      (L : Algebra.SquareJacobianPresentation.CoefficientLift I P),
      Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing ∧
        ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
          ∀ x : L.LiftRing,
            e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  sorry

end Algebra
