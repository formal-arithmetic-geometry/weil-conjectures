module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality

/-! # Opposite Borels in semisimple rank one

Source: Milne, Algebraic Groups (2017), Theorem 20.16(a) implies (b),
Proposition 20.18 and Lemma 20.21, printed pp.412--415
(blueprint: lem-sfb-rank-one-opposite-borel-intersection).

Subgroup equality is equality of the embeddings up to a commuting group-scheme
isomorphism. The intersection is tested on every commutative algebra, retaining
nilpotents and imposing no condition on the characteristic.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A maximal torus in a reductive group of semisimple rank one belongs to exactly
 two Borel subgroups, whose scheme-theoretic intersection is that torus.
The radical is specified by its largest-subgroup property, and the quotient by its
represented fppf sheaf presentation; neither object is chosen from a postponed proof.

Source: Milne, Theorem 20.16(a) implies (b), Proposition 20.18 and Lemma 20.21,
printed pp.412--415 (blueprint: lem-sfb-rank-one-opposite-borel-intersection).

Proof plan (the seven steps of the DAG node):
1. The algebraically closed field is perfect. Apply
   lem-sfb-perfect-solvable-unipotent-torus to R. Its unipotent part is normal in G,
   hence trivial by reductivity; R is a torus. By lem-sfb-connected-action-torus-rigidity
   it is central. The quotient geometry lemma makes Q smooth and connected. A smooth
   connected solvable normal subgroup of Q pulls back to such a subgroup of G:
   its derived series ends in the commutative R, and then in 1. Maximality of R
   makes that subgroup trivial. Thus Q is semisimple, and
   lem-sfb-smooth-unipotent-solvable also makes it reductive. Apply
   lem-sfb-reductive-semisimple-rank-formula: R lies in T, S = T/R is a maximal
   one-dimensional torus in Q, and q⁻¹(S) = T scheme-theoretically.
2. By lem-sfb-quotient-borel-torus-images and the quotient subgroup correspondence,
   B ↦ q(B) and D ↦ q⁻¹(D) identify the Borels containing T and S. For the inverse
   direction the preimage is smooth connected and solvable, since its derived
   series ends in R. A maximal-dimensional solvable overgroup is Borel by
   lem-sfb-solvable-normal-subgroup-products, and the subgroup correspondence
   identifies it with the original preimage.
3. By lem-sfb-semisimple-rank-one-tangent-dimension choose λ : G_m ≅ S and
   dim Lie(Q) = 3. The self-centralizer lemma and
   lem-sfb-cocharacter-limit-smooth-structure give P± = U± ⋊ S and the direct sum
   Lie(Q) = Lie(U−) ⊕ Lie(S) ⊕ Lie(U+). The middle term has dimension one by
   dual numbers. Neither outer term vanishes: otherwise the tangent-generation
   lemma gives P± = Q, reductivity kills U±, and Q = S contradicts dimension.
   Both outer terms therefore have dimension one and both P± dimension two.
4. The U± are solvable by lem-sfb-smooth-unipotent-solvable, so P± are solvable.
   Any smooth connected solvable overgroup has tangent dimension two or three.
   The tangent-generation lemma identifies it respectively with P± or Q; the
   latter is impossible by semisimplicity. Thus P± are distinct Borels containing S.
5. By lem-sfb-torus-normalizer-borel-transitivity every Borel containing S is in
   the normalizer orbit of P+. The self-centralizer lemma identifies the kernel
   of the action on S with S. By lem-sfb-multiplicative-character-antiduality,
   Aut(G_m) = Aut(ℤ) has two elements, including in characteristic two. Since S
   fixes P+, the orbit has at most two members, and these are precisely P±.
6. For x in P+(A) ∩ P−(A), its λ-conjugation orbit extends across both 0 and ∞
   by lem-sfb-cocharacter-limit-smooth-structure. Every coordinate Laurent
   polynomial thus belongs to A[t] ∩ A[t⁻¹] = A, by uniqueness of coefficients,
   also when A has nilpotents. The orbit is constant, so after every algebra
   extension x centralizes S. The self-centralizer lemma gives x in S(A).
   Conversely S(A) belongs to both groups. Thus their intersection is S(A).
7. Pull P± back along q to B±. Steps 2 and 5 give exactly the two Borels containing
   T. Inverse images commute with intersections, so step 6 and q⁻¹(S) = T give
   B+(A) ∩ B−(A) = T(A) for every A. This is equality of the closed subgroup
   schemes, with no reducedness or characteristic restriction. -/
theorem rank_one_opposite_borel_intersection
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T R Q : Grp (Over (Spec (.of F)))) (i : T ⟶ G) (r : R ⟶ G) (q : G ⟶ Q)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hR : SolvableGroupStructure.IsAlgebraic R)
    (hQ : SolvableGroupStructure.IsAlgebraic Q)
    (hr : IsClosedSubgroupScheme r.hom.hom)
    (hrn : IsNormalSubgroupScheme r.hom.hom)
    (hRs : Smooth R.X.hom) (hRc : ConnectedSpace R.X.left)
    (hRsol : IsSolvableGroupScheme R.X)
    (hRmax : ∀ (N : Grp (Over (Spec (.of F)))) (n : N ⟶ G),
      IsClosedSubgroupScheme n.hom.hom → IsNormalSubgroupScheme n.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left → IsSolvableGroupScheme N.X →
      ∃ f : N ⟶ R, f ≫ r = n)
    (hq : IsFppfGroupQuotient r q)
    (hrank : ∀ (S : Grp (Over (Spec (.of F)))) (s : S ⟶ Q),
      ReductiveTorusCentralizer.IsMaximalTorus s → topologicalKrullDim S.X.left = 1) :
    ∃ (Bplus Bminus : Grp (Over (Spec (.of F)))) (bplus : Bplus ⟶ G) (bminus : Bminus ⟶ G),
      IsBorelGroupScheme bplus.hom.hom ∧ IsBorelGroupScheme bminus.hom.hom ∧
      (∃ tplus : T ⟶ Bplus, tplus ≫ bplus = i) ∧ (∃ tminus : T ⟶ Bminus, tminus ≫ bminus = i) ∧
      (¬ ∃ e : Bplus ≅ Bminus, e.hom ≫ bminus = bplus) ∧
      (∀ (B : Grp (Over (Spec (.of F)))) (b : B ⟶ G),
        IsBorelGroupScheme b.hom.hom → (∃ t : T ⟶ B, t ≫ b = i) →
        (∃ e : B ≅ Bplus, e.hom ≫ bplus = b) ∨ (∃ e : B ≅ Bminus, e.hom ≫ bminus = b)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra F A],
        Set.range (fun x : StandardGroupSchemes.affine F A ⟶ Bplus.X ↦ x ≫ bplus.hom.hom) ∩
          Set.range (fun x : StandardGroupSchemes.affine F A ⟶ Bminus.X ↦ x ≫ bminus.hom.hom) =
          Set.range (fun x : StandardGroupSchemes.affine F A ⟶ T.X ↦ x ≫ i.hom.hom) := by
  sorry

end AlgebraicGeometry
