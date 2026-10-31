/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
public import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalCalculation

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Orientation.OrientationCoordinateBoundaryPullback
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Orientation.OrientationLocalResidue

/-! # Global affine-line orientation and its geometric normalization

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-affine-line-orientation; Milne, Lectures on Etale Cohomology, Section 16
(blueprint: thm-pur-affine-line-orientation).

The auxiliary data record the published Gysin identification and a snake-normalized
support boundary. Restriction uses the actual derived kernel pullback, with its
adjunction-unit normalization, and the canonical pullback of the finite root line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The Kummer boundary defines a global orientation in the full finite-Tor constructible
category, and its supported restriction at every geometric point has residue one.
The residue isomorphism is normalized independently by the fibre coordinate boundary,
so it is the unique A-linear normalization of the rank-one local calculation.

Source: blueprint main-20261015, thm-pur-affine-line-orientation; Milne, Section 16,
Theorems 16.1 and 16.7, Proposition 16.11 and Example 16.3
(blueprint: thm-pur-affine-line-orientation).

Proof: (1) The affine-line datum gives the zero section and its quasi-compact complement.
Finite type over the algebraic closure of a finite field gives a finite dimension bound;
lem-exc-open-complement-known supplies the open-complement condition. The root line is
locally free of rank one by lem-pur-twist-sheaf-locally-free. The closed ambient adjoint,
closed-amplitude and closed-Tor statements give constructibility and finite Tor amplitude.
(2) Apply the normalized support exact sequence to coordinateKummer. The canonical
Gysin identification and evaluation on 1 yield the morphism from the coefficient unit.
Both objects are finite-Tor constructible, so fullness gives the stated category.
(3) For an arbitrary geometric point, relative Kummer base change pulls the coordinate
class to the fibre coordinate class, without a finite-type condition on that point.
(4) Support-sequence pair naturality and supportedHom_pullback identify its boundary
with pullback of the supported morphism. (5) Finite closed exchange and the exceptional
counit identify this with restriction of the orientation under the exceptional adjunction.
(6) The adjunct-counit identity proves the comparison without assuming exceptional base
change invertible. Etale-origin full faithfulness transports the result to the small
pro-etale site. (7) rankOne_local_calculation gives the unique A-linear residue taking
the coordinate boundary to 1, since ord_0(t)=1. Thus the same residue of the restricted
global orientation is 1. Empty schemes cause no exception to the construction. -/
theorem affineLine_orientation (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.derivedSheaf h Y false)) ∧
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.gysinValue h Y)) ∧
    (∀ q : ℤ, q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj (P.gysinValue h Y))) ∧
    (∃ (hj : QuasiCompact (openImmersion Y)) (c : ℕ),
      @Scheme.HasOpenComplementCondition P.Coefficient inferInstance inferInstance
        (Punctured Y) (Line Y) (openImmersion Y) inferInstance hj c) ∧
    ∃ D : OrientationSupportData P h Y,
    ∃ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
      D.support.hom (P.gysinHomToSections h Y m) = D.coordinateBoundary P h a ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
        (y : Spec (CommRingCat.of Ω) ⟶ Y)
        (_hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))),
        ∃ D' : OrientationSupportData P h (Spec (CommRingCat.of Ω)),
        ∃ p : proEtaleSupportHomTransport P (zeroSection Y)
          (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y),
        ∃ ρ : P.gysinSupport h (Spec (CommRingCat.of Ω)) ≅ ModuleCat.of P.Coefficient P.Coefficient,
          ρ.hom (D'.coordinateBoundary P h
            (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)))) = 1 ∧
          ρ.hom (P.orientationSupportRestriction h y p
            (D.support.hom (P.gysinHomToSections h Y m))) = 1 := by
  obtain ⟨_, ⟨d, hj, _, hopen⟩, _, _, _, _, _, hunit, hvalue, hzero, hreal⟩ :=
    P.affine_line_boundary_realization h Y a
  obtain ⟨χ, hb, eK, eI, ε, heK, heI, hε, ⟨c⟩, hcharts⟩ := hreal
  obtain ⟨b, edge, e, hbmap, hedgemap, hemap, _, _, _, hboundary⟩ := hcharts c
  let D : OrientationSupportData P h Y :=
    { comparison := c
      openCoefficient := b
      openCoefficient_spec := hbmap
      edge := edge
      edge_spec := hedgemap
      support := e
      support_spec := hemap
      boundary := c.supportBoundary
      boundary_exact := c.support_exact
      boundary_normalized := c.support_normalized }
  obtain ⟨m, hm, _⟩ := hboundary c.supportBoundary c.support_exact
  refine ⟨hunit, hvalue, hzero, ⟨hj, 2 * d, hopen⟩, D, m, hm, ?_⟩
  intro Ω _ _ _ y hy
  obtain ⟨D', ρ, hρ⟩ := P.orientation_local_residue h Ω
  obtain ⟨p, hp⟩ := P.orientation_coordinate_boundary_pullback h Y a D Ω y hy D'
  refine ⟨D', p, ρ, hρ, ?_⟩
  change ρ.hom (P.orientationSupportRestriction h y p
    (e.hom (P.gysinHomToSections h Y m))) = 1
  rw [hm]
  exact (congrArg ρ.hom hp).trans hρ

end WeilConjectures.PurityFiniteSetting
