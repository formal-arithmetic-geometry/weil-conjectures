/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.SixFunctors.FrobeniusCohomologyTransport
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
public import Sheaf.Paper.SfIntegralConstructible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent
public import Sheaf.TraceFormula.StrictQuotientConeAugmentation
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Normalized Frobenius transport on finite free coefficient sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-def-purity-conv,
def-weil-frobenius-coefficient-twists; Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-frobenius-transport-normalization).

Finite coefficients use multiplication, not an unspecified pullback isomorphism.
Integral coefficients use the entire-cone comparison and the actual completion unit.
The auxiliary definitions only name the coordinates of this single statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.PointFrobeniusNormalization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Additivity of the recorded finite pullback, reused from its existing theorem.
Source: blueprint finite comparison
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
instance finitePullbackAdditive (n : ℕ) :
    (integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).Additive :=
  integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n

/-- The coefficient module category at the size used by point transport.
Source: blueprint finite sections (blueprint: lem-pur-point-frobenius-transport-normalization). -/
instance finiteSectionsDerived (n : ℕ) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The degree-zero complex of a finite coefficient sheaf.
Source: blueprint coefficient-sheaf paragraph
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
abbrev finiteComplex (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj M

/-- The specified finite kappa, with intrinsic pullback as target.
Source: blueprint normalized finite comparison
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def finiteKappa (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :=
  inverseImagePullbackComparisonFiniteIntrinsic l (frobeniusPointIso D).hom E
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n K

/-- Localize a multiplication isomorphism, retaining both localization comparisons
and the unit-normalized intrinsic presentation. Source: blueprint finite lambda
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def finiteLambda (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (e : ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom
      n).mapHomologicalComplex (.up ℤ)).obj K ≅
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex (.up
          ℤ)).obj K) :=
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
          integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteLimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteColimits (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  (Functor.mapDerivedCategoryNatIso
      (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
        (Padic.coefficientExtensionRing l E (n + 1)))).symm.app
        (DerivedCategory.Q.obj K) ≪≫
    (integralOperationsLevelPullback l E (frobeniusPointIso D).hom
        n).mapDerivedCategoryFactors.app K ≪≫
    DerivedCategory.Q.mapIso e ≪≫
    ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app
        K).symm

/-- The canonical identity direct-image identification, uniquely induced from
the identity pullback and its derived adjunction. Source: blueprint identity square
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def finiteDirectId (n : ℕ) :=
  (((sfIntrinsicConstantModuleAdjunction (𝟙 (Spec (.of D.k)))
    (Padic.coefficientExtensionRing l E (n +
        1))).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (sfIntrinsicDerivedPullbackId (Padic.coefficientExtensionRing l E (n + 1))
          (Spec (.of D.k)))).rightAdjointUniq Adjunction.id

/-- Ordinary transport for the actual structural map id, expressed on M by the
canonical identity direct-image comparison. This is the ordinary cohomology recipe,
point transport followed by the specified exchange. Source: blueprint tau formula
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def finiteOrdinary (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map ((finiteDirectId D l E n).inv.app N) ≫
  frobeniusPointTransportFinite D l hl E n
    ((proEtaleConstantDerivedDirectImage (𝟙 (Spec (.of D.k)))
      (Padic.coefficientExtensionRing l E (n + 1))).obj N) ≫
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map
      ((FrobeniusExchange.finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (𝟙 (Spec (.of D.k))) (𝟙 (Spec (.of D.k)))
        (frobeniusPointIso D).hom (frobeniusPointIso D).hom
        ((Category.comp_id _).trans (Category.id_comp _).symm)).app N) ≫
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u +
      2, u + 1}.map ((finiteDirectId D l E n).hom.app
      ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj N))

/-- The derived image of a sheaf Weil isomorphism, with the single-complex
and exact inverse-image comparisons retained. Source: blueprint linear v
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def finiteSheafIso (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n)
    (v : (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M ≅ M) :=
  (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.app
      (finiteComplex D l E n M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) (.up ℤ) (0 : ℤ)).app M ≪≫
        (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso v)

/-- The finite assertion, including the sheafified multiplication coordinates and
the equality in the derived category for every linear v. Source: blueprint finite case
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def FiniteNormalization (n : ℕ)
    (M : integralOperationsFiniteModules l E (Spec (.of D.k)) n) : Prop :=
  ∃ e : ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
      (.up ℤ)).obj (finiteComplex D l E n M) ≅
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex (.up
          ℤ)).obj (finiteComplex D l E n M),
    (∀ (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : ((finiteComplex D l E n M).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      (e.hom.f i).val.app (op U)
        (b • ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
          (finiteComplex D l E n M)).f i).val.app (op U) x) =
        (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
          (op U) b • x) ∧
    (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
      (finiteComplex D l E n M) = e.inv) ∧
    finiteKappa D l hl E n (finiteComplex D l E n M) ≫
      (finiteLambda D l E n (finiteComplex D l E n M) e).hom = 𝟙 _ ∧
    (finiteDerivedPullback l E n (frobeniusPointIso D).hom).map
        ((finiteDirectId D l E n).hom.app (DerivedCategory.Q.obj (finiteComplex D l E n M))) =
      (FrobeniusExchange.finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (𝟙 (Spec (.of D.k))) (𝟙 (Spec (.of D.k)))
        (frobeniusPointIso D).hom (frobeniusPointIso D).hom
        ((Category.comp_id _).trans (Category.id_comp _).symm)).app
          (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
      (finiteDirectId D l E n).hom.app
        ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj (finiteComplex D l E n M))) ∧
    (∀ v : (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).obj M ≅ M,
      finiteOrdinary D l hl E n (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (
      n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
            ((finiteLambda D l E n (finiteComplex D l E n M) e).hom ≫ (finiteSheafIso D l E n M
              v).hom) =
        frobeniusPointFiniteSigmaDerived D l E n
          (DerivedCategory.Q.obj (finiteComplex D l E n M)) ≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (
      n + 1))).mapDerivedCategory.{u + 2, u + 1}.map (finiteSheafIso D l E n M v).hom)

/-- Degree zero for the completed module sheaf, using the recorded unbounded category.
Source: blueprint integral case (blueprint: lem-pur-point-frobenius-transport-normalization). -/
abbrev integralComplex (M : integralTowerModules l E (Spec (.of D.k))) :=
  (CochainComplex.singleFunctor _ (0 : ℤ)).obj M

/-- The actual reduction/limit adjunction used to realize the ordinary exchange.
Source: blueprint entire-system recipe
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
abbrev calculus := (FrobeniusExchange.models l E).system (Spec (.of D.k))

/-- Identity direct image on whole strict systems, fixed by its identity pullback
adjunction. Source: blueprint identity structural square
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def systemDirectId :=
  ((FrobeniusExchange.systemAdjunction l E (𝟙 (Spec (.of D.k)))).ofNatIsoLeft
    (integralComparisonSystemUnit l E (Spec (.of D.k)))).rightAdjointUniq Adjunction.id

/-- The canonical map from identity direct image to its input. The completion inverse
is the actual unit inverse on the stated complete domain. `inverseOrZero` only extends
this formula to ambient objects where that unit need not be invertible.
Source: blueprint identity-operation identification
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralDirectId
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((systemDirectId D l E).hom.app ((calculus D l E).reduction.obj N)) ≫
    GeneratorReduction.inverseOrZero ((calculus D l E).adjunction.unit.app N)

/-- The inverse identity-operation word: completion unit, then the strict identity
comparison. Source: blueprint identity-operation identification
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralDirectIdInv
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (calculus D l E).adjunction.unit.app N ≫
    (coefficientSequenceLimit l E (Spec (.of D.k))).map
      ((systemDirectId D l E).inv.app ((calculus D l E).reduction.obj N))

/-- The specified whole-system mate, realized on the constructible domain.
The invertibility of ell follows from the finite-field datum.
Source: blueprint ordinary exchange (blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralExchange
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  letI := frobeniusPointPrimeInvertible D l hl
  (FrobeniusExchange.integralExchange l E
    (FrobeniusExchange.systemDirect l E (𝟙 (Spec (.of D.k))))
    (frobeniusPointIso D).hom (frobeniusPointIso D).hom
    (FrobeniusExchange.systemExchange l E (𝟙 (Spec (.of D.k)))
      (frobeniusPointIso D).hom (frobeniusPointIso D).hom
      ((Category.comp_id _).trans (Category.id_comp _).symm))).app N

/-- Ordinary point cohomology transport through the actual identity direct image,
its specified exchange, and its identity-operation coordinates.
Source: blueprint ordinary transport
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralOrdinary
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  (pointFibreIntegralAmbient D l E).map (integralDirectIdInv D l E N.obj) ≫
    frobeniusPointTransportIntegral D l hl E
      ((FrobeniusExchange.integralDirectImage l E (𝟙 (Spec (.of D.k)))).obj N.obj) ≫
    (pointFibreIntegralAmbient D l E).map (integralExchange D l hl E N) ≫
    (pointFibreIntegralAmbient D l E).map
      (integralDirectId D l E ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj N.obj))

/-- The normalized integral lambda, retaining the entire-cone theta and the actual
completion-unit isomorphism epsilon. Source: blueprint integral lambda
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralLambda
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (θ : (integralDerivedPullback l E (frobeniusPointIso D).hom).obj N ≅
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj
        (((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj N))
    (ε : N ≅
      ((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj N) :=
  θ ≪≫ ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).mapIso ε).symm

/-- The derived image of an integral sheaf Weil isomorphism.
Source: blueprint completed-linear v
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def integralSheafIso (M : integralTowerModules l E (Spec (.of D.k)))
    (v : (inverseImageIntegralModules l E (frobeniusPointIso D).hom).obj M ≅ M) :=
  (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.app
      (integralComplex D l E M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (inverseImageIntegralModules l E (frobeniusPointIso D).hom) (.up ℤ) (0 : ℤ)).app M ≪≫
        (CochainComplex.singleFunctor _ (0 : ℤ)).mapIso v)

/-- Quotient coordinates of the integral comparison, with a strict tower
isomorphism and the entire Roos map, including both cone coordinates.
Source: blueprint completed-coefficient reductions; Stacks 08TC
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def IntegralQuotientNormalization
    (M : integralTowerModules l E (Spec (.of D.k))) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (_e : DerivedCategory.Q.obj P.obj ≅ DerivedCategory.Q.obj (integralComplex D l E M)),
  ∃ j : (integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P.obj ≅
      (trfInverseImageTower l E (frobeniusPointIso D).hom).obj
        ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj),
    (∀ (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U)))
      (b : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U)),
      ((j.hom.app (op n)).f i).val.app (op U)
        (b • (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).obj
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U) x))) =
        (inv (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n)).hom.app
          (op U) b • x) ∧
    (∀ (n : ℕ) (i : ℤ) (U : (Spec (.of D.k)).ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i).val.obj
        (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U))),
      ((j.inv.app (op n)).f i).val.app (op U) x =
        (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).obj
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P.obj).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U) x))) ∧
  ∃ η : (trfInverseImageComplex l E (frobeniusPointIso D).hom).obj
      (integralOperationsRoos ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj)) ≅
    integralOperationsRoos ((trfInverseImageTower l E (frobeniusPointIso D).hom).obj
      ((trfQuotientTowerFunctor l E (Spec (.of D.k))).obj P.obj)),
    η.hom ≫ CochainComplex.mappingCocone.fst
        (trfInverseQuotientDifference l E (frobeniusPointIso D).hom P.obj) =
      (trfInverseImageComplex l E (frobeniusPointIso D).hom).map
        (CochainComplex.mappingCocone.fst (trfQuotientDifference l E (Spec (.of D.k)) P.obj)) ≫
      trfQuotientProductComparison l E (frobeniusPointIso D).hom P.obj ∧
    (∀ p : ℤ, η.hom.f (p + 1) ≫
        (CochainComplex.mappingCocone.snd
          (trfInverseQuotientDifference l E (frobeniusPointIso D).hom P.obj)).v
            (p + 1) p (add_neg_cancel_right p 1) =
      (inverseImageIntegralModules l E (frobeniusPointIso D).hom).map
        ((CochainComplex.mappingCocone.snd
          (trfQuotientDifference l E (Spec (.of D.k)) P.obj)).v
            (p + 1) p (add_neg_cancel_right p 1)) ≫
        (trfQuotientProductComparison l E (frobeniusPointIso D).hom P.obj).f p) ∧
    inverseImageRoosComparisonComplex l E (frobeniusPointIso D).hom P.obj ≫
        integralOperationsRoosFunctor.map j.hom =
      (trfInverseImageComplex l E (frobeniusPointIso D).hom).map
        (trfStrictQuotientConeAugmentation l E (Spec (.of D.k)) P.obj) ≫ η.hom

/-- The localization at the size of integral point sections.
Source: blueprint integral point-fibre convention
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
instance integralSectionsDerived :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The standard localization at the common size of field-valued point sections.
Source: blueprint common-stage coefficient convention
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
instance fieldSectionsDerived (F : Type u) [Field F] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} F)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The ordinary rational scalar-extension functor on actual derived sections.
Source: blueprint rational versions (blueprint: lem-pur-point-frobenius-transport-normalization).
-/
abbrev rationalExtension :=
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).mapDerivedCategory.{u + 1, u + 1}

/-- The common-stage extension from E to an algebraically closed coefficient field.
The source is the rational image of this same integral stage.
Source: blueprint common finite stage
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def closedExtension (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (ι : E →ₐ[ℚ_[l]] Ω) :=
  frobeniusCohomologyCoefficientExtension
    (ι.toRingHom.comp (ULift.ringEquiv : ULift.{u + 1} E ≃+* E).toRingHom)

/-- Integral cancellation, the identity structural exchange, and the ordinary
transport equation, for the precise theta and actual completion unit.
Source: blueprint integral case (blueprint: lem-pur-point-frobenius-transport-normalization). -/
def IntegralNormalization
    (M : integralTowerModules l E (Spec (.of D.k)))
    (hM : sfIntegralConstructible l E (Spec (.of D.k))
      (DerivedCategory.Q.obj (integralComplex D l E M))) : Prop :=
  ∃ θ : (integralDerivedPullback l E (frobeniusPointIso D).hom).obj
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≅
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj
        (((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj
          (DerivedCategory.Q.obj (integralComplex D l E M))),
  ∃ ε : DerivedCategory.Q.obj (integralComplex D l E M) ≅
      ((calculus D l E).reduction ⋙ coefficientSequenceLimit l E (Spec (.of D.k))).obj
        (DerivedCategory.Q.obj (integralComplex D l E M)),
    IntegralQuotientNormalization D l E M ∧
    ε.hom = (calculus D l E).adjunction.unit.app
      (DerivedCategory.Q.obj (integralComplex D l E M)) ∧
    inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≫ θ.hom =
      (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map ε.hom ∧
    inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
        (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl)
        (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
      (integralLambda D l E _ θ ε).hom = 𝟙 _ ∧
    (integralDerivedPullback l E (frobeniusPointIso D).hom).map
      (integralDirectId D l E (DerivedCategory.Q.obj (integralComplex D l E M))) =
      integralExchange D l hl E ⟨_, hM⟩ ≫ integralDirectId D l E
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          (DerivedCategory.Q.obj (integralComplex D l E M))) ∧
    (∀ v : (inverseImageIntegralModules l E (frobeniusPointIso D).hom).obj M ≅ M,
      integralOrdinary D l hl E ⟨_, hM⟩ ≫
        (pointFibreIntegralAmbient D l E).map ((integralLambda D l E _ θ ε).hom ≫
          (integralSheafIso D l E M v).hom) =
      frobeniusPointIntegralSigmaDerived D l E
          (DerivedCategory.Q.obj (integralComplex D l E M)) ≫
        (pointFibreIntegralAmbient D l E).map (integralSheafIso D l E M v).hom ∧
      (rationalExtension l E).map (integralOrdinary D l hl E ⟨_, hM⟩) ≫
        (pointFibreRationalAmbient D l E).map ((integralLambda D l E _ θ ε).hom ≫
          (integralSheafIso D l E M v).hom) =
      (rationalExtension l E).map (frobeniusPointIntegralSigmaDerived D l E
          (DerivedCategory.Q.obj (integralComplex D l E M))) ≫
        (pointFibreRationalAmbient D l E).map (integralSheafIso D l E M v).hom ∧
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (ι : E →ₐ[ℚ_[l]] Ω),
        (closedExtension l E Ω ι).map
            ((rationalExtension l E).map (integralOrdinary D l hl E ⟨_, hM⟩)) ≫
          (closedExtension l E Ω ι).map ((pointFibreRationalAmbient D l E).map
            ((integralLambda D l E _ θ ε).hom ≫ (integralSheafIso D l E M v).hom)) =
        (closedExtension l E Ω ι).map ((rationalExtension l E).map
          (frobeniusPointIntegralSigmaDerived D l E
            (DerivedCategory.Q.obj (integralComplex D l E M)))) ≫
          (closedExtension l E Ω ι).map ((pointFibreRationalAmbient D l E).map (integralSheafIso
            D l E M v).hom)))

/-- The finite constant or completed commutative coefficient sheaf; its underlying
ring sheaf is exactly the one used by point restriction.
Source: blueprint coefficient convention
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def coefficientRing (a : Option ℕ) :
    Sheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1} :=
  match a with
  | none => completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of D.k))
  | some n => integralCoefficientCommRingSheaf.{u, u} l E (Spec (.of D.k)) n

/-- Coefficient fixing and restriction compatibility with the tensor bilinear map
and internal-Hom evaluation. In the canonical evaluation coordinates sigma is
restriction, so these are the tensor and dual diagrams after the recorded comparisons.
The Hom formula uses the coefficient sheaf as codomain, hence is exactly the
evaluation diagram for the dual. Source: Stacks 03EK, 03EM; blueprint tensor/dual clause
(blueprint: lem-pur-point-frobenius-transport-normalization). -/
def TensorDualNormalization (a : Option ℕ) : Prop :=
  (∀ b : pointRestrictionScalars.{u, u} l E a,
    (pointRestrictionCoefficientMap.{u, u} l E (frobeniusPointIso D).hom a).hom.app
        (op (ProEt.mk (𝟙 _)))
      ((pointRestrictionRing.{u, u} l E (Spec (.of D.k)) a).obj.map
        (pointRestrictionArrow (frobeniusPointIso D).hom).op
        (pointRestrictionScalarAt.{u, u} l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b)) =
      pointRestrictionScalarAt.{u, u} l E (Spec (.of D.k)) a (ProEt.mk (𝟙 _)) b) ∧
  (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose
        (ProEt.topology (Spec (.of D.k))) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientRing D l E a)))
      (_hM : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (_hN : ∃ r : ℕ, Nonempty (N ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (x : M.val.obj (op (ProEt.mk (𝟙 _)))) (y : N.val.obj (op (ProEt.mk (𝟙 _)))),
    ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} N).obj M).val.map
        (frobeniusPointRestriction D).op
        (purTensorSection (coefficientRing D l E a) M N (ProEt.mk (𝟙 _)) x y) =
      purTensorSection (coefficientRing D l E a) M N
        ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj (ProEt.mk (𝟙 _)))
        (M.val.map (frobeniusPointRestriction D).op x)
        (N.val.map (frobeniusPointRestriction D).op y)) ∧
  (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose
        (ProEt.topology (Spec (.of D.k))) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientRing D l E a)))
      (_hM : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free (ULift.{u + 1} (Fin r))))
      (_hN : N = SheafOfModules.unit _)
      (φ : (SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := coefficientRing D l E a) M
        N).val.obj
        (op (ProEt.mk (𝟙 _)))) (x : M.val.obj (op (ProEt.mk (𝟙 _)))),
    N.val.map (frobeniusPointRestriction D).op (φ.app (op (Over.mk (𝟙 _))) x) =
      (((SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := coefficientRing D l E a) M N).val.map
        (frobeniusPointRestriction D).op φ).app (op (Over.mk (𝟙 _))))
          (M.val.map (frobeniusPointRestriction D).op x))

end WeilConjectures.PointFrobeniusNormalization
