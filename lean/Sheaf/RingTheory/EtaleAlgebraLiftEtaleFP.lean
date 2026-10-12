module
public import Sheaf.RingTheory.JacobianPresentationLift
public import Mathlib.RingTheory.Etale.Basic
@[expose] public section
universe u v
namespace Algebra
/-- Etaleness and finite presentation of the coefficient lift.
Source: Stacks Project, Tag 04D1.
(blueprint: lem-exc-etale-algebra-lift-etale-fp)

Proof: use the quotient presentation with variables and relations indexed by Option (Fin m).
The old equations have no t term, so their partial derivatives with respect to t vanish. The
last equation t * Delta - 1 has t derivative Delta. Hence the full Jacobian is block triangular
with determinant Delta squared. In the quotient t * Delta = 1, making Delta and its square
units. Pair each old equation with its old variable and the last equation with t. This gives a
square Jacobian presentation; its etale theorem gives etaleness. Finally an etale algebra is
finitely presented, by the finite-presentation field of Algebra.Etale. -/
theorem coefficientLift_etale_fp
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra (A ⧸ I) B] {m : ℕ}
    (P : Algebra.SquareJacobianPresentation (A ⧸ I) B (Fin m))
    (L : Algebra.SquareJacobianPresentation.CoefficientLift I P) :
    Algebra.Etale A L.LiftRing ∧ Algebra.FinitePresentation A L.LiftRing := by
  sorry
end Algebra
