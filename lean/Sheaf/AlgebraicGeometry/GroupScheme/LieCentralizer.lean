module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Algebra.DualNumber

/-! # The scheme-theoretic centralizer of a tangent vector

Source: Milne, Algebraic Groups (2017), Proposition 17.76, printed p.377
(blueprint: def-sfb-lie-centralizer).

The condition is imposed on every test algebra, including nonreduced algebras.
Commuting with the canonical infinitesimal point means fixing the tangent vector
under the differential of conjugation. This specifies a representing subgroup;
it does not choose a scheme from an unproved existence statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- A closed subgroup represents the adjoint stabilizer of X precisely when its image
on every R-point is the set commuting with the scalar extension of the tangent point of X.
The constant lift R -> R[epsilon] and the extension k[epsilon] -> R[epsilon],
a + b epsilon |-> a + b epsilon (universal property of the dual numbers), are canonical.
By the conjugation identity of lem-sfb-affine-group-dual-number-calculus, this is exactly
Ad(g)(1 tensor X) = 1 tensor X, without testing only rational or reduced points.
Source: Milne, Proposition 17.76, printed p.377
(blueprint: def-sfb-lie-centralizer). -/
def IsLieCentralizer {k : Type u} [Field k]
    {G C : Grp (Over (Spec (.of k)))} (j : C ⟶ G) (X : Lie G.X) : Prop :=
  IsClosedSubgroupScheme j.hom.hom ∧
    ∀ (R : Type u) [CommRing R] [Algebra k R] (g : points G.X R),
      (∃ c : points C.X R, c ≫ j.hom.hom = g) ↔
        Commute (points.map G.X (TrivSqZeroExt.inlAlgHom k R R) g)
          (points.map G.X
            (DualNumber.lift ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps),
              DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩) (tangentPoint X))

end AlgebraicGeometry.GrpObj
