/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PointReductionUnits
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck

/-! # Strict point transport on simultaneous quotient complexes

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3)
(blueprint: lem-trf-point-transport-strict-quotient).

The index n means positive exponent n+1. All strict towers use the one integral
coefficient ring, with the published identity-on-sections scalar restriction comparison.
The derived target is the derived category of strict towers of modules, retaining
coherence before and after localization. No Roos realization is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Additivity of the published scalar restriction, exposed for termwise comparisons.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointRestrictionAdditive (n : ℕ) :
    (pointUnitIntegralRestriction l E n).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (pointReductionQuotient l E n)).Additive)

/-- The small localization of the coefficient-module category used by finite transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointModuleHasDerived (R : Type (u + 1)) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The published identity-on-sections comparison in each degree of a complex.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointRestrictionComplexIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K) ≅
      ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).obj
        (((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (pointUnitIntegralSectionsRestrictionIso D l E n).app (K.X i))
    (fun i j _ ↦ ((pointUnitIntegralSectionsRestrictionIso D l E n).hom.naturality
      (K.d i j)).symm)

/-- Exact scalar restriction with the localization sizes used by point transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
abbrev strictQuotientPointDerivedRestriction (n : ℕ) :=
  (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 1, u + 1}

/-- Gamma(kappa) after sigma, restricted to the single integral coefficient ring.
The outer comparisons are the published identity-on-sections scalar comparisons.
Source: blueprint clause (3), simultaneous quotient transport
(blueprint: lem-trf-point-transport-strict-quotient)
(blueprint: def-trf-point-transport-strict-quotient-models). -/
def strictQuotientPointMap (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P) ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P) :=
  (strictQuotientPointRestrictionComplexIso D l E n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).hom ≫
  ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).map
    (frobeniusPointFiniteSigma D l E n
        ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P) ≫
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map
          (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
            ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))) ≫
  (strictQuotientPointRestrictionComplexIso D l E n
    (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
      (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))).inv

/-- The canonical localization/sections comparison at a finite quotient, retaining
its integral action. Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointSectionsIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K)) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.mapIso
      (strictQuotientPointRestrictionComplexIso D l E n K) ≪≫
    ((pointUnitIntegralRestriction l E n).mapDerivedCategoryFactors.{u + 1, u + 1}.symm.app
      (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.symm.app K)

/-- The canonical target comparison with the recorded intrinsic finite pullback.
Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointTargetIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj
            (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
              ).mapHomologicalComplex (.up ℤ)).obj K))) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
              (DerivedCategory.Q.obj K))) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteLimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteColimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  exact
  strictQuotientPointSectionsIso D l E n
      (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
            ).mapDerivedCategoryFactors.symm.app K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((Functor.mapDerivedCategoryNatIso
            (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
              (Padic.coefficientExtensionRing l E (n + 1)))).app (DerivedCategory.Q.obj K)))

/-- Standard localization for coherent integral-module towers. This chooses only
Mathlib's localization, not representatives of any transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointTowersHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

private def finitePointMap (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K) ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj
          (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
            ).mapHomologicalComplex (.up ℤ)).obj K)) :=
  (strictQuotientPointRestrictionComplexIso D l E n K).hom ≫
    ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).map
      (frobeniusPointFiniteSigma D l E n K ≫
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map
          (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K)) ≫
    (strictQuotientPointRestrictionComplexIso D l E n
      (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
        ).mapHomologicalComplex (.up ℤ)).obj K)).inv


end WeilConjectures
