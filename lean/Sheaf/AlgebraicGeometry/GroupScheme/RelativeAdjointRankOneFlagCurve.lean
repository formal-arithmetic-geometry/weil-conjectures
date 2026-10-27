module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativePointedFlagCurve
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts

/-! # The relative pointed flag curve of an adjoint rank-one group

Source: Conrad, Reductive group schemes, Proposition 4.2.7, proof, pp.123--124,
and Theorem 2.3.6, pp.72--75
(blueprint: lem-sfb-relative-adjoint-rank-one-flag-curve).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Zariski locally on Spec A, an adjoint reductive group of geometric semisimple rank
one, with a given split maximal torus, has its pointed smooth proper flag curve.
The conclusion retains the quotient, the group action, the identity section, the
geometric projective-line and full automorphism-sheaf assertions, and arbitrary base change.

Source: Conrad, Proposition 4.2.7, proof, pp.123--124, before trivializing the curve;
Theorem 2.3.6, pp.72--75
(blueprint: lem-sfb-relative-adjoint-rank-one-flag-curve).

Proof plan, following the seven steps of the DAG:
1. Finite type over the Noetherian base implies finite presentation
   (lem-weil-pbc-finite-type-noetherian-finite-presentation). The centre commutes with
   base change by lem-sfb-relative-reductive-centre-weight-kernel. Apply
   lem-sfb-rank-one-adjoint-projective-linear on geometric fibres. Torus conjugacy
   (lem-sfb-borel-maximal-torus-conjugacy) and character duality
   (lem-sfb-relative-diagonalizable-character-duality) show that the split torus has
   rank one. Choose its splitting cocharacter lambda.
2. Set B = P_lambda using lem-sfb-relative-dynamic-subgroups. It is smooth, closed,
   finitely presented, geometrically connected and compatible with arbitrary base change.
   Constant conjugation orbits give T inside B. The cocharacter is regular on each
   geometric fibre; lem-sfb-regular-cocharacter-borel-description makes B a Borel there,
   and lem-sfb-borel-scheme-normalizer gives its scheme-theoretic self-normalization.
3. Apply lem-sfb-relative-smooth-subgroup-normalizer to represent N_G(B). The inclusion
   B into N is finitely presented: in affine coordinates its ideal is J/I, generated
   by the generators of J. Apply lem-sfb-flat-geometric-fibre-open-criterion to this
   inclusion, since B is flat and locally finitely presented and each geometric fibre
   is an isomorphism. Thus N = B even over a nonreduced base; N need not be flat.
4. On geometric fibres lambda has exponent plus or minus one by character duality.
   Its dynamic subgroup is triangular. Exchange coordinates if needed. The first-column
   map has triangular stabilizer and local determinant-one lifts on both standard charts,
   by lem-weil-pbc-projective-space-standard-charts. Together with
   lem-sfb-projective-frames-pgl this identifies the fppf quotient with P1, with its action,
   on all test schemes and in every characteristic.
5. Apply lem-sfb-relative-self-normalizing-quotient: its hypotheses hold by steps 2--4.
   This gives a smooth proper representing scheme, without a relative matrix model.
6. Left multiplication descends by (g,hB) to ghB. The group identities give both action
   identities. The identity coset gives the section fixed by B. The quotient's arbitrary
   base-change property, and the corresponding property of B, pull back these formulas
   to the same action and section after every base change.
7. In step 4's geometric coordinates the action is the standard projective matrix action.
   Apply lem-sfb-projective-frames-pgl with two coordinates to identify the entire
   automorphism sheaf with the acting geometric group, not just its geometric points. -/
theorem exists_relativeAdjointRankOneFlagCurve
    (A : Type u) [CommRing A] [Nontrivial A] [IsNoetherianRing A]
    (G T : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (iT : T ⟶ G) [IsClosedImmersion iT.hom.hom.left]
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ RingGroupSchemes.splitTorus A r))
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A)),
      ReductiveTorusCentralizer.IsReductive ((Over.pullback t).mapGrp.obj G))
    (hrank : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A)),
      RankOneRoots.HasSemisimpleRankOne ((Over.pullback t).mapGrp.obj G))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of A)),
      ReductiveTorusCentralizer.IsMaximalTorus ((Over.pullback t).mapGrp.map iT))
    (hcenter : ∀ (V : Over (Spec (.of A))) (g : V ⟶ G.X),
      (∀ (W : Over (Spec (.of A))) (f : W ⟶ V) (h : W ⟶ G.X),
        Commute (f ≫ g) h) → g = 1) :
    ∀ s : Spec (.of A), ∃ U : (Spec (.of A)).Opens, s ∈ U ∧
      Nonempty (RelativePointedFlagCurve ((Over.pullback U.ι).mapGrp.obj T)
        ((Over.pullback U.ι).mapGrp.obj G) ((Over.pullback U.ι).mapGrp.map iT)) := by
  sorry

end AlgebraicGeometry
