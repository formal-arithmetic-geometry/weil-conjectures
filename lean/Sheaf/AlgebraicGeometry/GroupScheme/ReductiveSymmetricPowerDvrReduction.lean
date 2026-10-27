module

public import Sheaf.AlgebraicGeometry.GroupScheme.InvariantSymmetricPowerLifting
public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductiveConditions
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.IntegerPrimeLocalizations
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples

/-! # Reduction of invariant symmetric-power lifting to the DVR case

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Theorem 9.7.5, reductions preceding the determinant argument, printed p.527;
Lemma 9.2.5(5), Proposition 9.3.1 and Proposition 9.5.1.
(blueprint: lem-sfb-reductive-symmetric-power-dvr-reduction)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry


/-- If invariant symmetric-power lifting holds for split semisimple simply connected
DVR groups with algebraically closed residue field, it holds for every reductive group
over every ring. All rational modules are allowed in both the premise and conclusion.

Source: Alper, Theorem 9.7.5, p.527, and Lemma 9.2.5(5), p.522.
(blueprint: lem-sfb-reductive-symmetric-power-dvr-reduction)

Proof plan:
1. For R = 0 take n = 1 and q = 0. Otherwise use
   lem-sfb-reductive-etale-integral-models and clauses (1),(4) of
   lem-sfb-invariant-power-base-change-descent to reduce to split reductive Z-models.
   Group isomorphisms transport the coactions and the same lifting problem.
2. For a split torus decompose the degree-one lift of 1 into character coefficients
   by lem-sfb-group-algebra-coaction-grading. Equivariance kills the images of all
   nonzero weights. The zero-weight coefficient is an invariant lift in degree one.
3. By lem-sfb-split-integral-radical-cover choose the torus radical quotient and its
   simply connected semisimple cover. Their base changes remain exact, with finite
   locally free central kernel, including in characteristics where it is nonreduced.
4. For each rational prime p use lem-weil-pbc-z-localizations-dvr. Choose an algebraic
   closure of F_p (lem-pc-algebraic-closure-exists-unique); perfection makes it a
   separable closure. The strict henselization has that residue field by
   lem-weil-pbc-strict-henselization-triples and lem-weil-pbc-etale-local-ring-triples.
   It is a DVR by lem-sc-strict-henselization-dvr, and the map is faithfully flat by
   lem-sc-strict-henselization-faithfully-flat.
5. Apply the premise to the simply connected cover over each such DVR. The quotient
   and extension clauses of lem-sfb-invariant-power-exact-sequences, together with
   the torus case, give lifting for the original integral model over that DVR.
6. Descend to Z_(p) using clause (2) of lem-sfb-invariant-power-base-change-descent.
   Clause (3) and the classification of maximal ideals of Z yield lifting over Z.
   Step 1 then gives the assertion over R. No step restricts the rational module
   to be finite, free or flat. -/
theorem reductive_symmetricPower_dvr_reduction
    (hDVR : ∀ (A : CommRingCat.{u}) [IsDomain A] [IsDiscreteValuationRing A]
      [IsAlgClosed (IsLocalRing.ResidueField A)]
      (H : Scheme.{u}) [H.Over (Spec A)] [GrpObj (H.asOver (Spec A))]
      [IsAffine H] [Flat (H ↘ Spec A)]
      [LocallyOfFinitePresentation (H ↘ Spec A)] [Smooth (H ↘ Spec A)],
      RelativeReductive.HasSimplyConnectedSemisimpleFibres (Grp.mk (H.asOver (Spec A))) →
      RelativeReductive.HasSplitBorelPair (Grp.mk (H.asOver (Spec A))) →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H, ⊤))
    (R : CommRingCat.{u}) (G : Scheme.{u}) [G.Over (Spec R)]
    [GrpObj (G.asOver (Spec R))] [IsAffine G]
    [LocallyOfFinitePresentation (G ↘ Spec R)] [Smooth (G ↘ Spec R)]
    (hG : RelativeReductive.HasReductiveFibres (Grp.mk (G.asOver (Spec R)))) :
    InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} R Γ(G, ⊤) := by
  sorry

end AlgebraicGeometry
