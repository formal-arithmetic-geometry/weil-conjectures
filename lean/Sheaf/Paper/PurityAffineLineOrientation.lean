/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.PurityGysinStructure
public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.AlgebraicGeometry.SupportComparisonBoundary
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.Paper.PurityRankOneLocalCalculation

import Sheaf.AlgebraicGeometry.OpenComplementKnown
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.PurityAffineLineDatum
import Sheaf.Paper.PurityRelativeKummer
import Sheaf.Paper.SupportedCohomologyHom

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

/-- The canonical support chart of lem-pur-gysin-structure together with the actual
snake boundary. The formulas fix both the identification and its sign; none of the
maps is an unconstrained support isomorphism.
Source: blueprint main-20261015, Gysin identification and orientation construction
(blueprint: thm-pur-affine-line-orientation). -/
structure OrientationSupportData (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) where
  comparison : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
  openCoefficient : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
    (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true
  openCoefficient_spec : openCoefficient.hom = P.gysinOpenCoefficient h Y
  edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
    (localClasses P Y 2).obj (P.gysinClosed h Y)
  edge_spec : edge.hom = (comparison.edge 2).app (P.gysinClosed h Y)
  support : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y
  support_spec : support.hom = (globalSectionsFunctor (Modules P) Y).map
      (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
        (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
      edge.inv ≫ (comparison.supportIso 2).hom.app (P.gysinEtaleInput h Y)
  boundary : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤
  boundary_exact : Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
    (supportRestrictionArrow (zeroSection Y)) ⊤ boundary
  boundary_normalized : supportBoundaryNormalization (Scheme.ProEt.topology (Line Y))
    P.Coefficient (supportRestrictionArrow (zeroSection Y)) boundary

/-- The actual supported coordinate boundary in the published Gysin chart.
Source: blueprint orientation construction, pur_s sends 1 to the boundary of kappa(t)
(blueprint: thm-pur-affine-line-orientation). -/
def OrientationSupportData.coordinateBoundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y : Scheme.{u}}
    (D : OrientationSupportData P h Y) (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.gysinSupport h Y :=
  (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩
    (P.gysinKummerSection h Y a D.comparison D.openCoefficient)

/-- Canonical inverse image of the affine-line coefficient complex, through comparison
and the scalar-extended root pullback. This is defined for arbitrary base morphisms.
Source: blueprint affine-line datum and geometric-fibre paragraph
(blueprint: thm-pur-affine-line-orientation). -/
def orientationInputPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y) :
    (upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)).mapDerivedCategoryPlus.obj
      (P.gysinInput h Y) ⟶ P.gysinInput h T :=
  (supportHomDerivedComparison P (AffineSpace.map (ULift.{u} (Fin 1)) f)).inv.app
      (P.gysinEtaleInput h Y) ≫
    (nuPlus P (Line T)).map
      ((Functor.mapDerivedCategoryPlusSingleFunctor
          (Etale.upperStar (Modules P) (AffineSpace.map (ULift.{u} (Fin 1)) f)) 0).hom.app
          (P.twistEtale h (Line Y)) ≫
        (DerivedCategory.Plus.singleFunctor (EtSheaves P (Line T)) 0).map
          (P.twistEtalePullback h (AffineSpace.map (ULift.{u} (Fin 1)) f)))

/-- Pullback on the actual supported cohomology, with the canonical coefficient map.
The transport's supportUnit_spec fixes the underived kernel map by its inclusion;
derivedMap is its published right-derived base-change map.
Source: Milne, Section 9; blueprint orientation proof, restriction to a geometric point
(blueprint: thm-pur-affine-line-orientation). -/
def orientationSupportRestriction (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (f : T ⟶ Y)
    (p : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T)
      (AffineSpace.map (ULift.{u} (Fin 1)) f)) :
    P.gysinSupport h Y ⟶ P.gysinSupport h T :=
  (DerivedCategory.Plus.homologyFunctor (Modules P) 2).map
      ((p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback
        (AffineSpace.map (ULift.{u} (Fin 1)) f))).app (P.gysinInput h Y)) ≫
    (Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology (Line T)) (Modules P)
      (supportRestrictionArrow (zeroSection T)) 2).map (P.orientationInputPullback h f)

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
  sorry

end WeilConjectures.PurityFiniteSetting
