/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.TraceFormula.StrictQuotientConeAugmentation
public import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Sites.Sheafification
import all Sheaf.Paper.PointQuotientAugmentationDiagram
import all Sheaf.Paper.IsomorphismComparisonNatural
import all Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted

/-! # Strict naturality of point cone lifts

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), point-transport
supplement, original steps 1, 2 and 6; Stacks Tags 03EK, 03D6 and 08TC
(blueprint: lem-trf-point-cone-lifts-chain-naturality).

Index n denotes positive exponent n+1. All maps are the published strict tensor,
coefficient-reduction and signed mapping-cocone maps, before localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures.CompletedStalk
namespace WeilConjectures.PointConeLifts

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict section tower D(P), with the original quotient transitions.
Source: blueprint rational Frobenius integral model (3); Stacks 03EK
(blueprint: lem-trf-point-cone-lifts-chain-naturality). -/
abbrev reductionSections :=
  trfQuotientTowerFunctor l E (Spec (.of D.k)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sectionsComplex D l E)

/-- The strict restricted finite-pullback tower C(P), with coefficient-induced transitions.
Source: blueprint rational Frobenius integral model (3); Stacks 03D6
(blueprint: lem-trf-point-cone-lifts-chain-naturality). -/
abbrev pullbackTower := integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom

/-- The strict section tower B(P)=Gamma C(P), with integral scalars.
Source: blueprint rational Frobenius integral model (3); Stacks 03D6
(blueprint: lem-trf-point-cone-lifts-chain-naturality). -/
abbrev pullbackSections := pullbackTower D l E ⋙
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sectionsComplex D l E)

/-- The canonical a_P: take sections of the existing quotient augmentation and
use the uniquely normalized comparison on both cone coordinates.
Source: blueprint rational Frobenius integral model (3); Stacks 08TC
(blueprint: lem-trf-point-cone-lifts-chain-naturality). -/
def reductionLift (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (sectionsComplex D l E).obj P ⟶
      integralOperationsRoos ((reductionSections D l E).obj P) :=
  (sectionsComplex D l E).map (trfStrictQuotientConeAugmentation l E (Spec (.of D.k)) P) ≫
    (sectionsRoos D l E ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P)).hom

/-- The e_P associated to a strict tower map u(P), using the actual diagonal cone map.
Source: blueprint rational Frobenius integral model (3); Stacks 08TC
(blueprint: lem-trf-point-cone-lifts-chain-naturality). -/
def transportedLift
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (v : (reductionSections D l E).obj P ⟶ (pullbackSections D l E).obj P) :=
  reductionLift D l E P ≫ integralOperationsRoosMap v

/-- The strict quotient, inverse-image, Roos-coordinate, and section naturality
components needed for the final transported-lift calculation.
Source: blueprint main-20261015, rational Frobenius integral model proof (3),
point-transport supplement; (blueprint: lem-trf-point-cone-lifts-chain-naturality).
The proof is the simultaneous sectionwise tensor and mapping-cone calculation from
Stacks Tags 03EK, 03D6, 08TC. It records all five strict component equalities,
including the zero shifted coordinates, before the final functorial composition. -/
theorem pointConeLifts_components (_hl : l ≠ D.p) :
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj (n + 1) ≫
          (unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P.obj =
        unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      inverseImageReductionTheta l E (frobeniusPointIso D).hom (n + 1) P.obj ≫
          (integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P.obj =
        inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) (i : ℤ),
      (reductionLift D l E P.obj).f i ≫
          roosFirst ((reductionSections D l E).obj P.obj) n i =
        ((sectionsComplex D l E).map
          (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n)).f i ∧
      (reductionLift D l E P.obj).f i ≫
          roosSecond ((reductionSections D l E).obj P.obj) n i = 0 ∧
      (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj).f i ≫
          roosFirst ((pullbackTower D l E).obj P.obj) n i =
        (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj).f i ∧
      (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj).f i ≫
          roosSecond ((pullbackTower D l E).obj P.obj) n i = 0) ∧
    (∀ (X Y : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : X ⟶ Y),
      (∀ (n : ℕ) (i : ℤ),
        (integralOperationsRoosMap f).f i ≫ roosFirst Y n i =
          roosFirst X n i ≫ (f.app (op n)).f i ∧
        (integralOperationsRoosMap f).f i ≫ roosSecond Y n i =
          roosSecond X n i ≫ (f.app (op n)).f (i + -1)) ∧
      (sectionsComplex D l E).map (integralOperationsRoosMap f) ≫
          (sectionsRoos D l E Y).hom =
        (sectionsRoos D l E X).hom ≫
          integralOperationsRoosMap (Functor.whiskerRight f (sectionsComplex D l E))) ∧
    (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (h : P.obj ⟶ P'.obj),
      (∀ n : ℕ,
        (sectionsComplex D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ≫
            (((reductionSections D l E).map h).app (op n)) =
          (sectionsComplex D l E).map h ≫
            (sectionsComplex D l E).map
              (unrestrictedTowerUnit l E (Spec (.of D.k)) P'.obj n)) ∧
      (∀ n : ℕ,
        inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj ≫
            (((pullbackTower D l E).map h).app (op n)) =
          (trfInverseImageComplex l E (frobeniusPointIso D).hom).map h ≫
            inverseImageReductionTheta l E (frobeniusPointIso D).hom n P'.obj) ∧
      reductionLift D l E P.obj ≫
          integralOperationsRoosMap ((reductionSections D l E).map h) =
        (sectionsComplex D l E).map h ≫ reductionLift D l E P'.obj ∧
      inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj ≫
          integralOperationsRoosMap ((pullbackTower D l E).map h) =
        (trfInverseImageComplex l E (frobeniusPointIso D).hom).map h ≫
          inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P'.obj) := by
  sorry

/-- Strict quotient units, inverse-image theta lifts and sectionwise cone comparisons
are chain natural, including both coordinates and the zero shifted coordinates.

Source: blueprint main-20261015, rational Frobenius integral model proof (3),
point-transport supplement, original steps 1, 2 and 6; Stacks 03EK, 03D6, 08TC
(blueprint: lem-trf-point-cone-lifts-chain-naturality).

Proof, following the eight steps of the node:
1. Reduction sends x tensor 1 to x tensor 1, commutes with differentials and
restrictions, and gives equal maps after the unique sheafification extension.
2. The finite comparison sends y to y tensor 1. Its coefficient-induced transition
commutes with reduction, so v_n theta_(n+1)=theta_n. The completed coefficient
projection equation makes these maps R-linear.
3. The two compatible tuples j satisfy (1-s)j=0. The signed differential sends
(0,jz) to (-(1-s)jz,djz)=(0,jdz), giving both chain lifts and their zero coordinate.
4. For a strict tower map f, naturality gives (1-s_Y) product(f)=product(f)(1-s_X).
Thus its diagonal action on both product coordinates commutes with the differential.
5. Project to each shifted and unshifted coordinate of the normalized sections
comparison: both composites are Gamma(f_n) in that coordinate. Joint determination
by these projections proves strict comparison naturality.
6. On pure tensors h_n r_n=r'_n h and h_C,n kappa=kappa' g^{-1}(h_n).
Sheafification extends these equalities uniquely, and coefficient reduction proves
that the induced maps are strict tower maps.
7. Substitute these equalities in the two diagonal cone coordinates. Their shifted
coordinates remain zero because all component maps are linear.
8. Apply functoriality of the diagonal cone map to h_B u(P)=u(P') h_D, assumed only
for the given h, then use step 7. This yields H(h_B)e_P=e_P' Gamma(h) as chain maps.
-/
theorem pointConeLifts_chain_naturality (_hl : l ≠ D.p) :
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj (n + 1) ≫
          (unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P.obj =
        unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ),
      inverseImageReductionTheta l E (frobeniusPointIso D).hom (n + 1) P.obj ≫
          (integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P.obj =
        inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) (i : ℤ),
      (reductionLift D l E P.obj).f i ≫
          roosFirst ((reductionSections D l E).obj P.obj) n i =
        ((sectionsComplex D l E).map
          (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n)).f i ∧
      (reductionLift D l E P.obj).f i ≫
          roosSecond ((reductionSections D l E).obj P.obj) n i = 0 ∧
      (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj).f i ≫
          roosFirst ((pullbackTower D l E).obj P.obj) n i =
        (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj).f i ∧
      (inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj).f i ≫
          roosSecond ((pullbackTower D l E).obj P.obj) n i = 0) ∧
    (∀ (X Y : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : X ⟶ Y),
      (∀ (n : ℕ) (i : ℤ),
        (integralOperationsRoosMap f).f i ≫ roosFirst Y n i =
          roosFirst X n i ≫ (f.app (op n)).f i ∧
        (integralOperationsRoosMap f).f i ≫ roosSecond Y n i =
          roosSecond X n i ≫ (f.app (op n)).f (i + -1)) ∧
      (sectionsComplex D l E).map (integralOperationsRoosMap f) ≫
          (sectionsRoos D l E Y).hom =
        (sectionsRoos D l E X).hom ≫
          integralOperationsRoosMap (Functor.whiskerRight f (sectionsComplex D l E))) ∧
    (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (h : P.obj ⟶ P'.obj),
      (∀ n : ℕ,
        (sectionsComplex D l E).map (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ≫
            (((reductionSections D l E).map h).app (op n)) =
          (sectionsComplex D l E).map h ≫
            (sectionsComplex D l E).map
              (unrestrictedTowerUnit l E (Spec (.of D.k)) P'.obj n)) ∧
      (∀ n : ℕ,
        inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj ≫
            (((pullbackTower D l E).map h).app (op n)) =
          (trfInverseImageComplex l E (frobeniusPointIso D).hom).map h ≫
            inverseImageReductionTheta l E (frobeniusPointIso D).hom n P'.obj) ∧
      reductionLift D l E P.obj ≫
          integralOperationsRoosMap ((reductionSections D l E).map h) =
        (sectionsComplex D l E).map h ≫ reductionLift D l E P'.obj ∧
      inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj ≫
          integralOperationsRoosMap ((pullbackTower D l E).map h) =
        (trfInverseImageComplex l E (frobeniusPointIso D).hom).map h ≫
          inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P'.obj) ∧
    (∀ (v : ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        (reductionSections D l E).obj P.obj ⟶ (pullbackSections D l E).obj P.obj)
      (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (h : P.obj ⟶ P'.obj),
      v P ≫ (pullbackSections D l E).map h = (reductionSections D l E).map h ≫ v P' →
        transportedLift D l E P.obj (v P) ≫
            integralOperationsRoosMap ((pullbackSections D l E).map h) =
          (sectionsComplex D l E).map h ≫ transportedLift D l E P'.obj (v P'))  := by
  have hc := pointConeLifts_components D l E _hl
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, ?_⟩
  intro v P P' h hv
  unfold transportedLift
  have hred := (hc.2.2.2.2 P P' h).2.2.1
  calc
    (reductionLift D l E P.obj ≫ integralOperationsRoosMap (v P)) ≫
        integralOperationsRoosMap ((pullbackSections D l E).map h) =
      reductionLift D l E P.obj ≫
        integralOperationsRoosMap ((reductionSections D l E).map h ≫ v P') := by
          rw [Category.assoc, ← integralOperationsRoosMap_comp, hv,
            integralOperationsRoosMap_comp]
    _ = (sectionsComplex D l E).map h ≫
          reductionLift D l E P'.obj ≫ integralOperationsRoosMap (v P') := by
      rw [integralOperationsRoosMap_comp, ← Category.assoc, hred, Category.assoc]

end WeilConjectures.PointConeLifts
