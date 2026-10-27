module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange

/-! # The central torus radical and semisimple quotient of a reductive group

Source: Milne, Algebraic Groups (2017), Corollary 17.62(b)--(d), pp.372--373,
Sections 6.44--6.46, p.135, and Chapter 19(a)--(b), pp.397--400
(blueprint: lem-sfb-reductive-radical-quotient).

The radical is specified by its inclusion and largest-subgroup universal property.
Centrality uses the universal centre functor on all algebras. Base change says that
this very inclusion again satisfies the radical universal property, hence identifies
the closed subgroup with the geometric radical, independently of its presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reductive group has a radical which is its largest central subtorus; its
algebraic-closure base change is the geometric radical, and its represented fppf
quotient is geometrically semisimple and reductive.

Source: Milne, Algebraic Groups (2017), Corollary 17.62(b)--(d), pp.372--373,
Sections 6.44--6.46, p.135, and Chapter 19(a)--(b), pp.397--400
(blueprint: lem-sfb-reductive-radical-quotient).

Proof plan:
1. Among smooth connected solvable normal closed subgroups choose R of greatest
   dimension. The product with any other such N has the same properties by
   lem-sfb-solvable-normal-subgroup-products. Strict dimension growth for proper
   closed inclusions forces RN = R, giving the largest-subgroup property. Do the
   same over the algebraic closure to obtain C.
2. Apply lem-sfb-perfect-solvable-unipotent-torus to C. Its unipotent part is normal
   in the smooth ambient group, so reductivity makes it trivial and C is a torus.
   The base change of R lies in C by lem-sfb-solvable-normal-subgroup-products;
   lem-sfb-multiplicative-type-largest-subtorus makes this smooth connected closed
   subgroup a torus. Thus R is a torus.
3. The conjugation action on R is trivial by lem-sfb-connected-action-torus-rigidity,
   so every point of R is central after every change of scalar algebra.
4. By lem-sfb-affine-group-centre-base-change the centre is closed and commutative;
   lem-sfb-reductive-centre-multiplicative-type makes it of multiplicative type.
   Its largest subtorus exists and is smooth connected by
   lem-sfb-multiplicative-type-largest-subtorus. It is central, hence normal, and
   commutative, hence solvable, so it lies in R. Conversely R is a central torus,
   proving equality with that largest subtorus.
5. Repeat over the algebraic closure. Base change for the centre and its largest
   subtorus, from the two cited lemmas, identifies the pulled-back R with C.
   This proves radical base change only for the reductive group in question.
6. Apply lem-sfb-affine-normal-quotient-geometry to R in G. It represents exactly
   the fppf coset sheaf by an affine finite-type smooth geometrically connected Q,
   and identifies its geometric fibre with G over the algebraic closure modulo C.
7. Pull a smooth connected solvable normal subgroup S of the geometric Q back to P
   in geometric G. The quotient geometry lemma gives an exact sequence with kernel C
   and quotient S; P is smooth connected and normal. Pull back a solvable series of S
   and append one of C, so P is solvable. Maximality forces P = C and then S = 1.
   This is semisimplicity. By lem-sfb-smooth-unipotent-solvable every smooth unipotent
   subgroup is solvable, so Q is reductive as well. -/
theorem reductive_radical_quotient {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) (hG : ReductiveTorusCentralizer.IsReductive G) :
    ∃ (R : Grp (Over (Spec (.of k)))) (i : R ⟶ G),
      SolvableGroupStructure.IsAlgebraic R ∧ Smooth R.X.hom ∧ ConnectedSpace R.X.left ∧
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      SolvableGroupStructure.IsSolvable R ∧
      (∀ (N : Grp (Over (Spec (.of k)))) (j : N ⟶ G),
        SolvableGroupStructure.IsAlgebraic N → Smooth N.X.hom → ConnectedSpace N.X.left →
        IsClosedSubgroupScheme j.hom.hom → IsNormalSubgroupScheme j.hom.hom →
        SolvableGroupStructure.IsSolvable N → ∃ f : N ⟶ R, f ≫ i = j) ∧
      MultiplicativeType.IsTorus R ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
        (r : StandardGroupSchemes.affine k A ⟶ R.X),
        r ≫ i.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) ∧
      (∀ (T : Grp (Over (Spec (.of k)))) (j : T ⟶ G),
        IsClosedSubgroupScheme j.hom.hom → MultiplicativeType.IsTorus T →
        (∀ (A : Type u) [CommRing A] [Algebra k A]
          (t : StandardGroupSchemes.affine k A ⟶ T.X),
          t ≫ j.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A) →
        ∃ f : T ⟶ R, f ≫ i = j) ∧
      SolvableGroupStructure.IsAlgebraic
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj R) ∧
      Smooth ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj R).X.hom ∧
      ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj R).X.left ∧
      IsClosedSubgroupScheme
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i).hom.hom ∧
      IsNormalSubgroupScheme
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i).hom.hom ∧
      SolvableGroupStructure.IsSolvable
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj R) ∧
      (∀ (N : Grp (Over (Spec (.of (AlgebraicClosure k)))))
        (j : N ⟶ (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G),
        SolvableGroupStructure.IsAlgebraic N → Smooth N.X.hom → ConnectedSpace N.X.left →
        IsClosedSubgroupScheme j.hom.hom → IsNormalSubgroupScheme j.hom.hom →
        SolvableGroupStructure.IsSolvable N →
        ∃ f : N ⟶ (MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj R,
          f ≫ (MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i = j) ∧
      ∃ (Q : Grp (Over (Spec (.of k)))) (q : G ⟶ Q),
        IsFppfGroupQuotient i q ∧ ReductiveTorusCentralizer.IsReductive Q ∧
        IsSemisimpleGroupScheme
          ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj Q).X := by
  sorry

end AlgebraicGeometry
