/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm
import WeilConjectures.Mathlib.RingTheory.Localization.NormTrace

/-!
# Almost invariant functions for finite scheme groupoids

Source: Stacks Project, More on Groupoid Schemes, Tag 0ABF,
`lemma-find-almost-invariant-function`
(blueprint: lem-sfb-finite-groupoid-almost-invariant-function).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A boundary ideal contains a function whose inverse-image principal open is affine,
invariant under the groupoid, and contains all the marked points.

Source: Stacks Project, More on Groupoid Schemes, Tag 0ABF,
`lemma-find-almost-invariant-function`
(blueprint: lem-sfb-finite-groupoid-almost-invariant-function).

Since finite morphisms are quasi-compact and quasi-separated, the finite-presentation
assumptions are expressed by `LocallyOfFinitePresentation` together with `IsFinite`.
The orbit of `x k` is exactly `t '' (s ⁻¹' {x k})`, without rationality assumptions.

Proof:
1. If m = 0, take h = 0 in I. Its principal open is empty, hence affine, and both
   inverse images under s and t are empty (`def-weil-affine-spectrum`).
2. The immersion into Spec A makes U separated, hence quasi-separated, using
   `lem-weil-pbc-affine-source-morphism-separated`,
   `lem-trf-immersion-over-separated-base` and `lem-pc-separated-quasi-separated`.
   Apply `lem-sfb-finite-groupoid-generic-affine-flat-thickening` to get invariant
   affine V and an affine thickening V' containing the marked points, with finite
   locally free restricted arrows. Put B = Gamma(V', O).
3. The closed set C = V(I) union j(U) has j(V) open in it. Its closed complement is
   Z = V(I) union j(U minus V). Let K be its vanishing ideal and J = I intersect K.
   Then V(J) = Z, J is contained in I, and V(J) union j(V') = C; use the spectrum
   and immersion definitions `def-weil-affine-spectrum`, `def-weil-closed-immersion`.
4. Finite fibres make the union of the marked orbits finite. The thickening preserves
   these orbits: its defining ideals vanish in every residue field. By prime avoidance
   choose f in J nonvanishing on this union; write b for its image in B. Use
   `lem-weil-pbc-finite-closed-map-finite-fibres`, `lem-weil-pbc-prime-avoidance` and
   `lem-sfb-finite-groupoid-generic-affine-flat-thickening`.
5. Take g = Norm_s'(t'^sharp(b)) using `lem-pd-finite-locally-free-norm-charts`.
   By `lem-a1-affine-groupoid-invariant-norm`, D(g) is invariant. The criterion
   `lem-pd-finite-free-norm-prime-criterion` shows that it contains the marked points.
   The identity arrow shows D(g) is contained in D(b). This allows nilpotents and
   varying local rank, and uses the finite and groupoid definitions.
6. The immersion (V')_b into D_A(f) has closed image C intersect D_A(f), hence is
   a closed immersion (`lem-weil-pbc-immersion-closed-image-closed-immersion`).
   Factor through a closed immersion into an ambient open, composing closed
   immersions by `lem-weil-pbc-closed-immersion-comp` and then an open immersion
   (`def-weil-closed-immersion`, `def-weil-open-immersion`). Therefore A_f maps onto B_b.
   Lift g/1 to a/f^k. Some l satisfies b^l(phi(a) - b^k*g) = 0. Set h = f^(l+1)*a
   in J and n = k+l+1 > 0. Then phi(h) = b^n*g and D_A(h) is contained in D_A(f).
   Use `def-weil-ring-localization-away` and
   `lem-weil-pbc-affine-open-section-vanishing-prime` for this localization step.
7. W = j inverse-image D_A(h) lies in V and pulls back to D(g) on V'. The thickening
   identifies the underlying spaces of V' and V and of their restricted arrows.
   Thus invariance descends to V. Outside its restricted arrows neither endpoint
   lies in V, so W is invariant on all R. The marked points lie in W. Finally W is
   a principal open of affine V, hence affine, by
   `lem-weil-pbc-affine-open-section-vanishing-prime`. -/
theorem finiteGroupoid_exists_almostInvariant_function
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    [IsFinite s] [IsFinite t]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]
    (m : ℕ) (x : Fin m → U)
    (hOrbit : ∀ (k : Fin m) (y : U), y ∈ t '' (s ⁻¹' {x k}) →
      ∃ Z ∈ irreducibleComponents U, IsGenericPoint y Z)
    (A : CommRingCat.{u}) (j : U ⟶ Spec A) [IsImmersion j] (I : Ideal A)
    (hDisjoint : Set.range j ∩ PrimeSpectrum.zeroLocus (I : Set A) = ∅)
    (hClosed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪ Set.range j)) :
    ∃ h ∈ I, IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
      (∀ k : Fin m, x k ∈ j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
      s ⁻¹ᵁ (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) =
        t ⁻¹ᵁ (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) := by
  sorry

end AlgebraicGeometry
