module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus

/-! # Existence and uniqueness of the unipotent radical

Source: Milne, Algebraic Groups, Proposition 6.42, p.134, and Section 6.46, p.135;
matrix interpretation in Corollary 14.12 and Section 14(c), pp.283, 286--287
(blueprint: lem-sfb-unipotent-radical-existence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected affine finite-type group over an algebraically closed field has
one largest smooth connected closed normal unipotent subgroup scheme, its unipotent
radical. Uniqueness means an isomorphism commuting with the inclusions in the ambient
group, hence equality as closed subgroup schemes. The trivial ambient group is included.
Source: Milne, Proposition 6.42 and Section 6.46, pp.134--135
(blueprint: lem-sfb-unipotent-radical-existence).

Proof:
1. The trivial subgroup is a candidate: its structure morphism is the identity, so it
   is smooth and finite type (def-sbc-smooth-morphisms, def-weil-finite-type-morphism),
   and its space is a point (def-weil-connected-scheme). The identity section is closed
   because its coordinate homomorphism to F is surjective (def-weil-closed-immersion).
   It is normal (def-sc-group-scheme-subgroup); its closed representation in GL_1 is
   the identity matrix, which is unipotent (def-sfb-solvable-group-structure).
2. Every candidate is solvable (lem-sfb-smooth-unipotent-solvable).
   By lem-sfb-solvable-normal-subgroup-products, H is geometrically connected,
   candidate dimensions are nonnegative integers bounded by dim H, and proper closed
   inclusions between smooth connected groups strictly increase dimension.
   Choose a candidate U of greatest dimension. Algebraic closedness makes F perfect:
   every minimal polynomial splits, so all algebraic extensions are trivial
   (def-weil-algebraic-closure).
3. For any other candidate V, lem-sfb-solvable-normal-subgroup-products constructs
   P = UV, smooth connected closed normal and solvable, containing both candidates,
   with its fppf-local product description. Apply
   lem-sfb-perfect-solvable-unipotent-torus to P to obtain its unipotent part P_u and
   torus quotient q. That theorem's containment assertion puts both U and V in P_u.
4. For every F-algebra B and x in P(B), the local-product description gives a faithfully
   flat finitely presented extension C/B with x_C = uv. Both factors lie in P_u(C),
   so q(x)_C = 1. The represented quotient is an fppf sheaf, and equality descends to
   q(x) = 1. Its scheme-theoretic kernel is P_u (def-sfb-solvable-group-structure),
   so P = P_u as subgroup schemes. Thus P is itself a candidate, without assuming
   the existence of the unipotent radical in advance.
5. A proper inclusion U in P would strictly increase dimension, contrary to the choice
   of U. Hence P = U and V is contained in U, proving greatestness. Any other greatest
   candidate contains U and is contained in U. Their defining ideals have both reverse
   inclusions, hence coincide (def-weil-closed-immersion); equivalently their subgroup
   inclusions are isomorphic over H. If H is trivial, the trivial candidate is already
   greatest, so the resulting subgroup is H itself. -/
theorem exists_unipotent_radical {F : Type u} [Field F] [IsAlgClosed F]
    (H : Grp (Over (Spec (.of F)))) (hH : SolvableGroupStructure.IsAlgebraic H)
    (hsm : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) :
    ∃ (U : Grp (Over (Spec (.of F)))) (i : U ⟶ H),
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      SolvableGroupStructure.IsUnipotent U ∧
      (∀ (V : Grp (Over (Spec (.of F)))) (j : V ⟶ H),
        Smooth V.X.hom → ConnectedSpace V.X.left →
        IsClosedSubgroupScheme j.hom.hom → IsNormalSubgroupScheme j.hom.hom →
        SolvableGroupStructure.IsUnipotent V → ∃ f : V ⟶ U, f ≫ i = j) ∧
      (∀ (V : Grp (Over (Spec (.of F)))) (j : V ⟶ H),
        Smooth V.X.hom → ConnectedSpace V.X.left →
        IsClosedSubgroupScheme j.hom.hom → IsNormalSubgroupScheme j.hom.hom →
        SolvableGroupStructure.IsUnipotent V →
        (∀ (W : Grp (Over (Spec (.of F)))) (l : W ⟶ H),
          Smooth W.X.hom → ConnectedSpace W.X.left →
          IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
          SolvableGroupStructure.IsUnipotent W → ∃ f : W ⟶ V, f ≫ j = l) →
        ∃ e : V ≅ U, e.hom ≫ i = j) := by
  sorry

end AlgebraicGeometry
