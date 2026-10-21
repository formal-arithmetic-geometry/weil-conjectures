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
import Sheaf.Paper.PointAutomorphismRestrictionNatural
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Localization.Predicate

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
(blueprint: lem-trf-point-transport-strict-quotient). -/
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

/-- Strict quotient, augmentation and chain-map identities, followed by coherent
localization descent and the prescribed finite point-transport evaluations.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3) (blueprint: lem-trf-point-transport-strict-quotient).

Proof:
1. Use lem-weil-point-automorphism-restriction-natural for the integral coefficient
   action on P and on every restricted quotient. Its restriction/colimit-insertion/
   sheafification maps are the same underlying sigma maps at every coefficient level.
   The square pi_n c_integral = c_finite g_inverse(pi_n) makes tensor insertion
   completed-linear: kappa(c_integral_inverse(a)x) = x tensor pi_n(a).
2. The actual transition v_n sends x tensor b to g_inverse(t_n)(x) tensor rho_n(b).
   The coefficient naturality of lem-weil-proetale-isomorphism-inverse-image makes
   this balanced. On the sheafified generators, v_n kappa = kappa g_inverse(t_n).
   This uses def-pur-sheaf-tensor-product, not separately chosen derived quotients.
3. Naturality of sigma for t_n gives Gamma(t_n) followed by u_n equal to u_(n+1)
   followed by Gamma(v_n). These are strict equalities of integral-linear chain maps;
   def-weil-inverse-system then supplies the strict tower morphism.
4. The specified theta is kappa g_inverse(r_n). Naturality of sigma for r_n gives
   Gamma(r_n) followed by u_n equal to sigma_P followed by Gamma(theta_n).
5. For f:P to P', tensor insertion commutes with f tensor 1 on every section, and
   sigma is natural by lem-weil-point-automorphism-restriction-natural. This gives
   the displayed strict chain-map naturality and functoriality of the two towers.
6. By lem-pur-derived-change-of-rings, quotient tensor preserves quasi-isomorphisms
   between K-flat complexes; no quotient-flatness is needed. Finite pullback along
   the automorphism is exact. Restriction changes only the scalar action, and exact
   point sections from lem-weil-point-proetale-sections-exact preserve these maps.
7. The abelian tower category is supplied by
   lem-weil-pbc-small-module-diagrams-grothendieck; its kernels and cokernels are
   levelwise. Rearrange the same strict towers as complexes of towers, using the
   displayed natural coordinate identifications. The homotopies obtained by tensor,
   inverse image and sections commute with all transitions, by the formulas of step 5.
8. Apply lem-weil-pbc-site-derived-tensor-descent to the good resolving class, then
   lem-weil-pbc-localization-universal-property to descend both functors and their
   transformation. The comparison equation holds for every good representative.
   Uniqueness is localization extensionality. For a roof, naturality for its inverted
   quasi-isomorphism and its forward map proves independence and derived naturality.
9. The source is sections of def-weil-pbc-adic-coefficient-datum's coherent reduction
   tower for O_E and (varpi), computed by the actual strict quotients of P. Its maps
   and augmentations are those of def-weil-integral-reduction-tower. The target uses
   the corresponding finite pullbacks. For sfIntegralConstructible objects the
   finite reductions are bounded constructible. The finite evaluation equality below
   identifies the localized u_n with def-weil-frobenius-point-transport's iota,
   using only the identity-on-sections scalar comparison and the unit-normalized
   intrinsic-pullback comparison. The all-representative descent equation makes
   this identification independent of P. -/
theorem pointTransport_strictQuotient (hl : l ≠ D.p) :
    (∀ n : ℕ,
      inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom ≫
          limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) =
        (isoSectionwiseInverseImage (frobeniusPointIso D).hom RingCat.{u + 1}).map
            (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) ≫
          inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P.obj) ≫
          strictQuotientPointMap D l E n P.obj =
        strictQuotientPointMap D l E (n + 1) P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P.obj)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (unrestrictedTowerUnit l E (Spec (.of D.k)) P.obj n) ≫
          strictQuotientPointMap D l E n P.obj =
        frobeniusPointIntegralSigma D l E P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (n : ℕ) (i : ℤ) (V : (Spec (.of D.k)).ProEt)
      (x : (P.obj.X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj V))),
      ((inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj).f i).val.app
          (op V) x =
        ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
          ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).f i).val.app
            (op V)
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.obj.X i)
              (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj V)) 1 x)) ∧
    (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (f : P.obj ⟶ P'.obj) (n : ℕ),
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).map f) ≫
          strictQuotientPointMap D l E n P'.obj =
        strictQuotientPointMap D l E n P.obj ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
            ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).map f)) ∧
    (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory),
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
      ∀ n : ℕ,
        DerivedCategory.Q.map (strictQuotientPointMap D l E n P.obj) ≫
            (strictQuotientPointTargetIso D l E n
              ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).hom =
          (strictQuotientPointSectionsIso D l E n
              ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)).hom ≫
            (strictQuotientPointDerivedRestriction l E n).map
              (frobeniusPointTransportFinite D l hl E n
                (DerivedCategory.Q.obj
                  ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj)))) ∧
    ∃ (A B : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤
        CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ℤ)
      (eA : A ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
          (Functor.ofOpSequence (X := fun n ↦
            unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n)
            (unrestrictedIntegralTransition l E (Spec (.of D.k)))).flip ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)))
      (eB : B ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
          integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)))
      (V : A ⟶ B),
      (∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) (n : ℕ),
        ((eA.inv.app P ≫ HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (V.app P) ≫ eB.hom.app P).app (op n)) = strictQuotientPointMap D l E n P.obj) ∧
      (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (f : P ⟶ P'), QuasiIso f.hom → QuasiIso (A.map f) ∧ QuasiIso (B.map f)) ∧
      ∃ (F H : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
          DerivedCategory (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
        (eF : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅
          A ⋙ DerivedCategory.Q)
        (eH : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ H ≅
          B ⋙ DerivedCategory.Q),
        ∃! τ : F ⟶ H,
          ∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
            τ.app (DerivedCategory.Q.obj P.obj) ≫ eH.hom.app P =
              eF.hom.app P ≫ DerivedCategory.Q.map (V.app P) := by
  sorry

end WeilConjectures
