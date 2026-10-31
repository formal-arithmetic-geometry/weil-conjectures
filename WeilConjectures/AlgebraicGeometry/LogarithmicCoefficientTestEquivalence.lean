/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LogarithmicCoefficientIdeal
public import WeilConjectures.AlgebraicGeometry.RestrictedMarkedTests
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.AlgebraicGeometry.EtaleAtPointFromDifferentials
import WeilConjectures.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.MarkedControlledBlowupCharts
import WeilConjectures.AlgebraicGeometry.PermissibleCoordinateChart
import WeilConjectures.RingTheory.SmoothLocalTangentConeExtension
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Logarithmic coefficient restriction preserves every finite test

Source: ILO VIII 2.3.13, printed p.94; BMT, arXiv:0905.3580, sections 5.1--5.4,
especially the equivalence in section 5.4 following the coefficient-ideal formula
(blueprint: lem-trf-logarithmic-coefficient-test-equivalence).

The theorem and its companion clauses use actual ideal sheaves, cartesian pullback and
scheme-theoretic strict transforms. No nonvanishing of the coefficient ideal is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.MarkedIdeal
open HilbertSamuel

/-- Logarithmic coefficient restriction gives a coherent marked datum and preserves cosupport
and every finite test, including intervening open restrictions. All realizations of the same
coefficient ideal are covered, so no choice of support isomorphism changes the assertion.
Source: ILO VIII 2.3.13 and BMT 5.4
(blueprint: lem-trf-logarithmic-coefficient-test-equivalence).

Proof, following all thirteen steps of the node:
1. Smooth stalks are regular. Regular generators form a regular sequence and their associated
   graded ring is a polynomial ring over the residue field. Thus I^r lies in m^(rq) exactly
   when I lies in m^q. Apply this separately to each term of the weighted sum.
2. Derivations lower order by at most one. The cosupport of (K,d) lies in V(h) because
   h belongs to D_B^(d-1)K, and is contained in the coefficient cosupport.
3. Extend h and the boundary equations to etale coordinates. The implicit Taylor calculus
   supplies coefficients a_i=(partial_h^i f)|H/i!. Unique formally etale lifts give compatible
   expansions in each finite normal thickening; no algebraic product is asserted.
4. Comparing monomials in (m_H,h)^d identifies cosupport with the factorial-weighted sum
   of the normal coefficients A_i. This ideal is contained in the logarithmic coefficient
   ideal C, proving the reverse inclusion at stage zero, also at nonclosed points.
5. Induct on a common finite prefix. The single-transform logarithmic derivative inclusion
   keeps the transformed h in the last derivative ideal, hence keeps cosupport inside H'.
6. The marked controlled-blowup charts give h in the center ideal, identify strict supports
   with intrinsic blowups, and supply their smoothness. The h-chart has empty cosupport;
   tangent-coordinate charts have h=e*h'. Components used as centers disappear.
7. Substitute h=e*h' in the finite normal expansion. The coefficients with i<d divide by
   e^(d-i), and the other coefficients have nonnegative exceptional exponents. The center
   power containment guarantees all these coefficients are regular.
8. An exceptional boundary-intersection blowup leaves h unchanged and pulls back its normal
   coefficients without division. The coordinate charts remain regular and hence smooth.
   Line products pull back coefficients and append the independent horizontal zero section;
   open restriction just restricts the same calculation.
9. Restriction to H' commutes with each transform, and raising the jth term to L/(d-j)
   changes its exceptional denominator to e^L. Thus the tracked weighted sums are exactly
   the controlled transform of C and of the normal-coefficient ideal A.
10. At each prefix the normal-coefficient cosupport equals that of K', which is contained
    in that of C', which is contained in that of A'. Equality makes next centers permissible
    in both directions, and induction gives every finite word and subsequent cosupport.
11. Repeat this comparison for any h or representative and use transitivity. Coordinates
    only compute the intrinsically defined logarithmic differential ideals.
12. Logarithmic derivatives commute with smooth pullback. Smooth local tangent-cone
    extension preserves the degree of every nonzero initial form, hence every order threshold.
    The marked-blowup base-change theorem identifies strict supports, controlled ideals and
    each ordered boundary. The exceptional charts pull back to the same formulas.
13. If C vanishes on an open component of H its cosupport is that whole component.
    Blowing up the component deletes its strict transform, hence its coefficient cosupport.
    The finite-word equality gives the same disappearance for the original marked datum.
-/
theorem logarithmic_coefficient_test_equivalence
    {S : Embedded (ULift.{u} ℚ)} (M : Marked S) (D : LogCoefficientData M) :
    (∃ Q : Marked S, IsLogCoefficient D Q) ∧
      ∀ Q : Marked S, IsLogCoefficient D Q →
        M.cosupport = Q.cosupport ∧ RestrictedEquivalent M Q := by
  sorry

/-- Different maximal-contact sections, coordinate computations and equivalent original
representatives give equivalent coefficient presentations in the same ambient. No equality
between the two coefficient ideals is claimed. Source: BMT 5.2 and 5.4
(blueprint: lem-trf-logarithmic-coefficient-test-equivalence).

Proof: Step 11 of the node. Apply logarithmic_coefficient_test_equivalence to both
coefficient data. Its finite-word comparison, the supplied comparison of the representatives,
and transitivity identify every permissible center and every subsequent cosupport. For
coordinates or different h on one representative use the identity comparison of that datum.
-/
theorem logarithmic_coefficient_choices
    {S : Embedded (ULift.{u} ℚ)} (M P : Marked S)
    (D : LogCoefficientData M) (E : LogCoefficientData P)
    (hMP : RestrictedEquivalent M P) (Q R : Marked S)
    (hQ : IsLogCoefficient D Q) (hR : IsLogCoefficient E R) :
    Q.cosupport = R.cosupport ∧ RestrictedEquivalent Q R := by
  sorry

/-- The coefficient construction and its test identification commute with every smooth
pullback between finite-type rational ambients, including open restrictions and arbitrary
relative dimensions. The displayed maps are cartesian and the section is actually pulled back.
Source: BMT 5.1 and 5.4 and the smooth-pullback clause of the node
(blueprint: lem-trf-logarithmic-coefficient-test-equivalence).

Proof: Step 12. Pull back H, i and h cartesianly. Smooth base change preserves smoothness,
transversality and order one. The smooth local tangent-cone extension preserves every order
threshold, so it preserves maximal order near cosupport. The logarithmic derivative equality
commutes with restriction, finite sums and powers, giving the displayed equality of C. Apply
the main test comparison to this pulled-back datum. At each finite stage the actual schematic
strict supports are the base changes by the marked controlled-blowup theorem; its controlled
ideal and ordered-boundary formulas commute with the same change. Exceptional charts have
no division and line products append the pulled-back independent coordinate.
-/
theorem logarithmic_coefficient_smooth_pullback
    {S T : Embedded (ULift.{u} ℚ)} (M : Marked S) (D : LogCoefficientData M)
    (f : T.Z ⟶ S.Z) [Smooth f] (hfinite : QuasiCompact T.p)
    (hp : f ≫ S.p = T.p)
    (hB : T.boundary = S.boundary.map (fun B ↦ B.comap f))
    (M' : Marked T) (hM : MarkedPullback f M M') :
    M'.cosupport = f ⁻¹' M.cosupport ∧
    ∃ (D' : LogCoefficientData M') (g : M'.N ⟶ M.N) (q : D'.H ⟶ D.H),
      IsPullback g M'.j M.j f ∧ M'.ideal = M.ideal.comap g ∧
      IsPullback q D'.i D.i g ∧ D'.h = g.appTop D.h ∧
      logarithmicCoefficientIdeal (T.boundary.map (fun B ↦ B.comap M'.j))
        M'.ideal D'.i M'.marking =
      (logarithmicCoefficientIdeal (S.boundary.map (fun B ↦ B.comap M.j))
        M.ideal D.i M.marking).comap q ∧
      ∀ (Q : Marked S) (Q' : Marked T), IsLogCoefficient D Q →
        IsLogCoefficient D' Q' → MarkedPullback f Q Q' ∧
          Q'.cosupport = f ⁻¹' Q.cosupport ∧ RestrictedEquivalent M' Q' := by
  sorry

/-- A zero coefficient ideal has full cosupport on an open smooth component, and blowing
up that component deletes its cosupport. The center and transforms are the existing actual
ones, including when the entire hypersurface is a component or has dimension zero.
Source: BMT 5.1--5.2 and Step 13 of the coefficient-restriction node
(blueprint: lem-trf-logarithmic-coefficient-test-equivalence).

Proof: The zero ideal lies in every power of every maximal ideal. Thus every point of U is
in cosupport. Its ambient image is a smooth closed permissible center transverse to the
boundary. The marked controlled-blowup chart theorem identifies the new support with the
intrinsic blowup of H. The component U is contained in the center, so its strict transform is
empty. All its ambient inverse images therefore miss the transformed coefficient support;
the main finite-word equality gives the same cosupport disappearance for the original datum.
-/
theorem logarithmic_coefficient_zero_component
    {S : Embedded (ULift.{u} ℚ)} (M : Marked S) (D : LogCoefficientData M)
    (Q : Marked S) (hQ : IsLogCoefficient D Q) (U : D.H.Opens)
    (hU : (U : Set D.H) ∈ irreducibleComponents D.H)
    (hzero : (logarithmicCoefficientIdeal (S.boundary.map (fun B ↦ B.comap M.j))
      M.ideal D.i M.marking).comap U.ι = 0) :
    (D.i ≫ M.j) '' (U : Set D.H) ⊆ Q.cosupport ∧
    (∃ (T : Embedded (ULift.{u} ℚ)) (s : Step S T),
      s.kind = .admissibleBlowup ∧
      s.center = (U.ι ≫ D.i ≫ M.j).ker ∧ s.Admissible Q.cosupport) ∧
    ∀ (T : Embedded (ULift.{u} ℚ)) (s : Step S T) (Q' : Marked T),
      s.kind = .admissibleBlowup → s.center = (U.ι ≫ D.i ≫ M.j).ker →
      s.Admissible Q.cosupport → s.Transforms Q Q' →
        Q'.cosupport ∩ s.π ⁻¹' ((D.i ≫ M.j) '' (U : Set D.H)) = ∅ := by
  sorry

end AlgebraicGeometry.MarkedIdeal
