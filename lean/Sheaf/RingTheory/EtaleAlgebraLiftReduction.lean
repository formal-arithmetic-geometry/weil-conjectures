module
public import Sheaf.RingTheory.JacobianPresentationLift
@[expose] public section
universe u v
namespace Algebra
/-- The coefficient lift has the specified reduction isomorphism.
Source: Stacks Project, Tag 04D1.
(blueprint: lem-exc-etale-algebra-lift-reduction)

Proof: quotienting the lifted polynomial ring by the constants from I reduces its coefficients
to A/I. The old equations then become P.relation by L.map_relation, and partial derivatives
and determinants commute with this coefficient map. Quotienting further by the old equations
identifies their quotient with B by P's presentation property. The remaining equation is
therefore t * P.jacobian - 1. Since P.jacobian is a unit, evaluation at its inverse gives an
isomorphism B[t]/(t * P.jacobian - 1) to B: its inverse includes B as constants, and their
composites fix B and t, the latter because t * P.jacobian = 1 forces t to be that inverse.
Composing these identifications gives e. On coefficients, old variables, and t its composite
with the quotient map agrees with L.polynomialReduction; polynomial and quotient induction
therefore give e (mk x) = L.reduction x for every x. -/
theorem coefficientLift_reduction_equiv
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    ∃ e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B,
      ∀ x : L.LiftRing,
        e (Ideal.Quotient.mk (I.map (algebraMap A L.LiftRing)) x) = L.reduction x := by
  sorry
end Algebra
