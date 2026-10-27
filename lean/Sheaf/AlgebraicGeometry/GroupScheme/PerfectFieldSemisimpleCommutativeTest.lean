module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.FieldTheory.Perfect
import Sheaf.AlgebraicGeometry.SolvableGroupStructure

/-! # Semisimplicity tested by commutative normal subgroups

Source: Milne, Algebraic Groups (2017), Proposition 19.3, p.398; 6.44, p.135;
Propositions 19.1 and 19.2(a), pp.397--398.
(blueprint: lem-sfb-perfect-field-semisimple-commutative-test)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Over a perfect field, geometric semisimplicity is equivalent to triviality of
all smooth connected commutative closed normal subgroup schemes. Triviality means
that the identity section is an isomorphism, including all scheme structure.

Source: Milne, Algebraic Groups (2017), Proposition 19.3, p.398; geometric
semisimplicity is 6.44, p.135, and radical descent is 19.1 and 19.2(a), pp.397--398.
(blueprint: lem-sfb-perfect-field-semisimple-commutative-test)

Proof:
1. Compare finite-series solvability with termination of the derived series.
   Minimality of each derived subgroup places the iterated derived subgroup in
   the corresponding term of any commutative-quotient series. Conversely the
   derived series is such a series. Existence and smooth geometric connectedness
   of its terms use lem-sfb-solvable-normal-subgroup-products and
   lem-sfb-derived-commutator-word-arbitrary-field, with
   def-sfb-solvable-group-structure.
2. If G is geometrically semisimple, extend a subgroup N in the test to the
   algebraic closure. It stays smooth and connected by
   lem-sfb-solvable-normal-subgroup-products; normality, closedness and
   commutativity persist on every algebra of points. Its derived subgroup is
   trivial, so geometric semisimplicity makes it trivial. Descend this statement:
   write k[N] = k direct-sum I using the augmentation. Since I tensor kbar = 0,
   faithful field extension gives I = 0, and the identity section is an isomorphism
   (def-sc-group-scheme-subgroup and def-weil-affine-spectrum).
3. Choose a smooth connected solvable closed normal subgroup R of largest
   dimension. The trivial subgroup is a candidate, and dimensions are bounded
   nonnegative integers. The products and strict-dimension clauses of
   lem-sfb-solvable-normal-subgroup-products show every other candidate lies in R.
4. Perfection makes the algebraic closure a separable algebraic extension.
   Apply lem-sfb-solvable-radical-separable-base-change: R over that closure is
   still the largest smooth connected solvable normal subgroup. Thus R = 1
   implies geometric semisimplicity, without any reductivity assumption.
5. If the test holds but R is nontrivial, take its successive derived subgroups.
   The arbitrary-field derived-commutator theorem gives smooth geometrically
   connected terms. Inductively each is normal in G: conjugation by every point
   over every k-algebra restricts to an automorphism, and
   lem-sfb-derived-subgroup-universal-characteristic preserves the next term.
   Solvability provides a last nontrivial term.
6. That last term has trivial derived subgroup, hence is commutative on every
   algebra of points. It meets every hypothesis of the test, which makes its
   identity section an isomorphism, a contradiction. Therefore R = 1 and step 4
   applies. For G = 1 the radical is already trivial and the same argument applies.
-/
theorem perfectField_semisimple_iff_commutativeNormalSubgroups_trivial
    {k : Type u} [Field k] [PerfectField k]
    (G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hconn : ConnectedSpace
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left) :
    IsSemisimpleGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X ↔
    ∀ (N : Over (Spec (.of k))) [GrpObj N] [IsCommMonObj N] (i : N ⟶ G.X),
      IsClosedSubgroupScheme i → IsNormalSubgroupScheme i →
      Smooth N.hom → ConnectedSpace N.left → IsAffine N.left →
      LocallyOfFiniteType N.hom → QuasiCompact N.hom → IsIso η[N] := by
  sorry

end AlgebraicGeometry
