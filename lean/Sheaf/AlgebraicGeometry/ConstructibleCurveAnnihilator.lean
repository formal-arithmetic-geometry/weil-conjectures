module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.CurveCoefficientPair

/-- A constructible torsion sheaf on a curve is killed by a positive integer.
Source: Stacks Project, Definition 03RW and Lemma 095E; the finite-bound
argument in step 1 of the parent constructible subobject node, used for 09BH (2).

Proof: the finite constructible stratification of the sheaf has quasi-compact strata,
since the curve is Noetherian. Trivializing etale covers can therefore be replaced
by finite subcovers, because etale maps are open. Discard empty cover members.
On each remaining member the underlying set sheaf is constant, with a finite value:
its geometric stalk is finite, and a constant sheaf has its value as every stalk.
The orders of the abelian stalk groups on that member equal the cardinality of
this value, so that cardinality's factorial annihilates all those groups. Choose
the product of these finitely many positive factorials, using 1 if there are none.
Pullback identifies the stratum stalks with the stalks of the original sheaf.
Thus multiplication by this integer has zero geometric stalks everywhere.
Exactness of geometric stalks makes its image have zero stalks; conservativity
makes that image zero. Hence the multiplication morphism is zero.
The zero sheaf and the empty curve are covered by the choice of integer 1.
(blueprint: lem-weil-pbc-curve-constructible-annihilator) -/
theorem exists_annihilator_of_constructible {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k) (hF : P.IsConstructible) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 P.F = 0 := by sorry

end AlgebraicGeometry.CurveCoefficientPair
