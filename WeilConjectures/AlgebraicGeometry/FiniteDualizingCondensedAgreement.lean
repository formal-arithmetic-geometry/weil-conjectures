/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCondensedScalarCoordinates
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.FiniteDualizing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.CompactSupportRealizationCoordinates
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficientMaps

import WeilConjectures.AlgebraicGeometry.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation
import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjointComparisons
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import WeilConjectures.CategoryTheory.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
import WeilConjectures.SixFunctors.ScalarSixDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleScalarMateNormalization
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ScalarSixPullback
import WeilConjectures.SixFunctors.OpenScalarTensorNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.SixFunctors.ScalarSixCtf

/-! # Agreement of the two finite dualizing objects

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
prop-coef-integral-dualizing.proof.md, first paragraph, compatibility with reductions.
(blueprint: lem-coef-finite-dualizing-condensed-agreement).

The comparison is expressed in ordinary fixed-scalar coordinates. The condensed object
and counit are transported through the normalized section-action encoding. The other
object is the exact comparison pullback of the ordinary etale dualizing object. All
compactifications below are retained parameters, identical at every coefficient level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteCondensedDualizing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite coefficient ring is given its discrete topology.
Source: finite-stage coefficient identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
instance coefficientTopologicalSpace (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥

/-- Discreteness of the chosen coefficient topology.
Source: finite-stage coefficient identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
instance coefficientDiscreteTopology (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) :=
  discreteTopology_bot _

include l E

/-- Finiteness at every positive level, from the recorded coefficient construction.
Source: Serre, Local Fields, II.2 and the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
instance coefficientFinite (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The existing finite quotient, as a bundled discrete condensed coefficient ring.
The level n denotes exponent n+1. Source: the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def ring (n : ℕ) : ScalarSixRing.{u} :=
  ⟨cartesianFinitePointRing (Padic.coefficientExtensionRing l E (n + 1))⟩

/-- The recorded normalized coefficient encoding, with the discrete topology fixed.
Source: the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def EncodingAt (n : ℕ) (T : Scheme.{u}) :=
  Encoding (Padic.coefficientExtensionRing l E (n + 1)) T

/-- The listed quotient on condensed rings: postcompose each continuous section with
its actual quotient homomorphism. Source: the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def quotient {m n : ℕ} (h : n ≤ m) : ring l E m ⟶ ring l E n := by
  let φ := finiteDualizingQuotientBase l E h
  let q : Profinite.continuousCoefficientRingSheaf
      (Padic.coefficientExtensionRing l E (m + 1)) ⟶
      Profinite.continuousCoefficientRingSheaf
        (Padic.coefficientExtensionRing l E (n + 1)) :=
    ⟨{ app P := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((φ.compLeftContinuous P.unop continuous_of_discreteTopology).comp
              ULift.ringEquiv.toRingHom))
       naturality _ _ _ := rfl }⟩
  exact CommMon.homMk (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map q))

/-- Normalized scalar coordinates for the actual quotient.
Source: the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def ScalarCoordinates {m n : ℕ} (h : n ≤ m) (T : Scheme.{u})
    (EA : EncodingAt l E m T) (EB : EncodingAt l E n T) :=
  FiniteCondensedScalarCoordinates (finiteDualizingQuotientBase l E h)
    (quotient l E h) T EA EB

/-- The coefficient unit in internal coordinates, constructed by the inverse normalized
encoding. Source: the finite-stage identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def unit (n : ℕ) (T : Scheme.{u}) (e : EncodingAt l E n T) :=
  e.fixedDerived.inverse.obj (𝟙_ _)

/-- Normalized comparison of inverse images, conjugate to the existing identity on
sections of direct images. Source: the coefficient identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def pullEncoding (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : EncodingAt l E n X) (eY : EncodingAt l E n Y) :
    CondensedRing.upperStar (ring l E n).X f ⋙
        (eX.ordinary.trans eX.fixed).functor ≅
      (eY.ordinary.trans eY.fixed).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) f := by
  let EX := eX.ordinary.trans eX.fixed
  let EY := eY.ordinary.trans eY.fixed
  let i := encodingPushforwardNatIso
    (Padic.coefficientExtensionRing l E (n + 1)) Y X f eY eX
  let k := Iso.isoCompInverse (H := EY) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EX) k
  exact ((EY.toAdjunction.comp (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) f)).leftAdjointUniq
    (((CondensedRing.upperStarLowerStarAdjunction (ring l E n).X f).comp
      EX.toAdjunction).ofNatIsoRight kr)).symm

/-- The open-extension comparison fixed by the recorded open adjunctions.
Source: the coefficient identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def openEncoding (n : ℕ) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (eX : EncodingAt l E n X) (eY : EncodingAt l E n Y) :
    CondensedRing.openImmersionLowerShriek (ring l E n).X j ⋙
        (eY.ordinary.trans eY.fixed).functor ≅
      (eX.ordinary.trans eX.fixed).functor ⋙
        ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) j := by
  let EX := eX.ordinary.trans eX.fixed
  let EY := eY.ordinary.trans eY.fixed
  let i := pullEncoding l E n j eX eY
  let k := Iso.isoCompInverse (H := EX) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EY) k
  exact ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (ring l E n).X j).comp
    EY.toAdjunction).leftAdjointUniq
      ((EX.toAdjunction.comp (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) j)).ofNatIsoRight kr.symm)

/-- The K-injective direct-image comparison, from the same sectionwise identity.
Source: the coefficient identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def pushEncoding (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : EncodingAt l E n X) (eY : EncodingAt l E n Y) :
    (CondensedRing.lowerStar (ring l E n).X f).rightDerivedFunctor ⋙
        eY.fixedDerived.functor ≅
      eX.fixedDerived.functor ⋙ (ProEtale.lowerStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) f).rightDerivedFunctor :=
by
  letI : (eY.ordinary.trans eY.fixed).functor.Additive :=
    inferInstanceAs (eY.ordinary.functor ⋙ eY.fixed.functor).Additive
  letI : (eX.ordinary.trans eX.fixed).functor.Additive :=
    inferInstanceAs (eX.ordinary.functor ⋙ eX.fixed.functor).Additive
  letI : (eX.ordinary.functor ⋙ eX.fixed.functor).Additive :=
    inferInstanceAs (eX.ordinary.trans eX.fixed).functor.Additive
  letI : (eY.ordinary.functor ⋙ eY.fixed.functor).Additive :=
    inferInstanceAs (eY.ordinary.trans eY.fixed).functor.Additive
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (encodingPushforwardNatIso (Padic.coefficientExtensionRing l E (n + 1))
        Y X f eY eX) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _

/-- Derived extension-by-zero comparison from the normalized open adjunction.
Source: the coefficient identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def derivedOpenEncoding (n : ℕ) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (eX : EncodingAt l E n X) (eY : EncodingAt l E n Y) :
    (CondensedRing.openImmersionLowerShriek (ring l E n).X j).mapDerivedCategory ⋙
        eY.fixedDerived.functor ≅
      eX.fixedDerived.functor ⋙ (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) j).mapDerivedCategory := by
  letI : (eY.ordinary.trans eY.fixed).functor.Additive :=
    inferInstanceAs (eY.ordinary.functor ⋙ eY.fixed.functor).Additive
  letI : (eX.ordinary.trans eX.fixed).functor.Additive :=
    inferInstanceAs (eX.ordinary.functor ⋙ eX.fixed.functor).Additive
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openEncoding l E n j eX eY) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The compact-support identification for the actual specified compactification,
with its canonical open and proper factors. Source: the coefficient identification paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def supportEncoding (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : ∀ T : Scheme.{u}, EncodingAt l E n T) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (ring l E n).X c ⋙
        (e Y).fixedDerived.functor ≅
      (e X).fixedDerived.functor ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushEncoding l E n c.g (e c.Z) (e Y)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (derivedOpenEncoding l E n c.i (e X) (e c.Z)) _ ≪≫
    Functor.associator _ _ _

/-- The canonical site comparison on the regular coefficient unit, using the published
single-complex and degree-zero unit comparisons. Source: the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def siteUnit (n : ℕ) (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) T).mapDerivedCategory.obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) T) ≅ 𝟙_ _ :=
  (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) T).mapDerivedCategory.mapIso
      (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) T).mapDerivedCategorySingleFunctor
        0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (ProEtale.comparisonUpperStarUnitIso (finiteDualizingCoeff l E n) T) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- Scalar extension of the regular unit, normalized by the site/tensor comparison and
ordinary multiplication B tensor_A A to B. Source: the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def scalarUnit {m n : ℕ} (h : n ≤ m) (T : Scheme.{u}) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology T)
      (finiteDualizingQuotient l E h)).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (pbcFixedScalarExtension (Scheme.ProEt.topology T)
      (finiteDualizingQuotient l E h)).mapIso (siteUnit l E m T).symm ≪≫
    (pbcComparisonReduction T (finiteDualizingQuotient l E h)).app
      (Etale.constantComplex (finiteDualizingCoeff l E m) T) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) T).mapDerivedCategory.mapIso
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) T) ≪≫
    siteUnit l E n T

/-- The internal scalar-unit identification, recovered by full faithfulness from its
normalized ordinary coordinate formula. Source: the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def internalScalarUnit {m n : ℕ} (h : n ≤ m) (T : Scheme.{u})
    (EA : EncodingAt l E m T) (EB : EncodingAt l E n T)
    (s : ScalarCoordinates l E h T EA EB) :
    (scalarSixChange (quotient l E h) T).obj (unit l E m T EA) ≅ unit l E n T EB :=
  EB.fixedDerived.fullyFaithfulFunctor.preimageIso
    (s.extension.app (unit l E m T EA) ≪≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology T)
        (finiteDualizingQuotient l E h)).mapIso (EA.fixedDerived.counitIso.app (𝟙_ _)) ≪≫
      scalarUnit l E h T ≪≫ (EB.fixedDerived.counitIso.app (𝟙_ _)).symm)

variable (D : FiniteFieldDatum.{u}) [Fact (l ≠ D.p)]
  (X : Over (Spec (.of D.k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (c : Compactification X.hom)

/-- The actual etale dualizing object, retaining c as the chosen compactification.
Source: the two dualizing objects in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def etaleObject (n : ℕ) :=
  letI := c.hasCompactification
  Etale.dualizingComplex (finiteDualizingCoeff l E n) X.hom

/-- The same etale dualizing object in D+, using the existing finite-amplitude bound.
Source: the comparison-class adjunction in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def etaleObjectPlus (n : ℕ) :=
  letI := c.hasCompactification
  (Etale.boundaryUpperShriekPlus (finiteDualizingCoeff l E n) X.hom).obj
    (Etale.boundaryCoefficientPlus (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The transported dualizing object, exactly nu_X^* of the etale dualizing object.
Source: object (2) in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def transported (n : ℕ) :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X.left).mapDerivedCategory.obj
      (etaleObject l E D X c n)

/-- The geometric counit: canonical compact-support site comparison, etale counit,
then the coefficient-unit site identification. It is the comparison-class counit.
Source: object (2) in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def transportedCounit (n : ℕ) :=
  letI := c.hasCompactification
  (ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n) c).hom.app
      (etaleObjectPlus l E D X c n) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
      (Spec (.of D.k))).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekIso (finiteDualizingCoeff l E n) c).hom.app
          (etaleObject l E D X c n)) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
      (Spec (.of D.k))).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction (finiteDualizingCoeff l E n)
          X.hom).counit.app
            (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))) ≫
    (siteUnit l E n (Spec (.of D.k))).hom

/-- The finite pro-etale realization of the actual counit-defined etale map u.
Source: clause (c) of the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def transportedReduction {m n : ℕ} (h : n ≤ m) :=
  letI := c.hasCompactification
  (pbcComparisonReduction X.left (finiteDualizingQuotient l E h)).hom.app
      (etaleObject l E D X c m) ≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X.left).mapDerivedCategory.map
        (Etale.ExceptionalCoefficients.dualizingScalarMap
          (finiteDualizingQuotient l E h) X.hom)

variable (enc : ∀ (n : ℕ) (T : Scheme.{u}), EncodingAt l E n T)
  (R : ∀ n : ℕ, ScalarExceptionalAdjoint (ring l E n) c)
  (hU : ∀ n : ℕ,
    (constantModelBoundedConstructible (ring l E n).X (Spec (.of D.k)) ⊓
      DerivedCategory.finiteTorAmplitude _)
        (unit l E n (Spec (.of D.k)) (enc n (Spec (.of D.k)))))

/-- The regular coefficient unit packaged in the recorded Dctf full category.
Source: object (1) in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def coefficientUnit (n : ℕ) :
    ConstantModelConstructibleFiniteTor (ring l E n).X (Spec (.of D.k)) :=
  ⟨unit l E n (Spec (.of D.k)) (enc n (Spec (.of D.k))), hU n⟩

/-- The condensed dualizing object in the common ordinary coordinates.
Source: object (1) in the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def condensed (n : ℕ) :=
  (enc n X.left).fixedDerived.functor.obj
    ((R n).upper.obj (coefficientUnit l E D enc hU n)).obj

/-- The condensed counit transported through the specified support encoding, with
its given localizing-adjunction normalization. Source: object (1)
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def condensedCounit (n : ℕ) :=
  (supportEncoding l E n c (enc n)).inv.app
      ((R n).upper.obj (coefficientUnit l E D enc hU n)).obj ≫
    (enc n (Spec (.of D.k))).fixedDerived.functor.map
      ((R n).counit (coefficientUnit l E D enc hU n)) ≫
    (enc n (Spec (.of D.k))).fixedDerived.counitIso.hom.app (𝟙_ _)

/-- The beta of scalarSixExceptional, followed by its normalized scalar-unit
identification and expressed in common ordinary coordinates. Source: clause (c)
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def condensedReduction {m n : ℕ} (h : n ≤ m)
    (ha : ListedCoefficientMap l (quotient l E h))
    (sX : ScalarCoordinates l E h X.left (enc m X.left) (enc n X.left))
    (sS : ScalarCoordinates l E h (Spec (.of D.k))
      (enc m (Spec (.of D.k))) (enc n (Spec (.of D.k)))) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let S : Over (Spec (.of D.k)) := Over.mk (𝟙 (Spec (.of D.k)))
  letI : LocallyOfFiniteType S.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  letI : QuasiCompact S.hom := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  letI : IsSeparated S.hom := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
  let us :
      (scalarExceptionalChange l D.k (quotient l E h) ha S).obj
          (coefficientUnit l E D enc hU m) ⟶ coefficientUnit l E D enc hU n :=
    ObjectProperty.homMk
      (internalScalarUnit l E h (Spec (.of D.k))
        (enc m (Spec (.of D.k))) (enc n (Spec (.of D.k))) sS).hom
  sX.extension.inv.app ((R m).upper.obj (coefficientUnit l E D enc hU m)).obj ≫
    (enc n X.left).fixedDerived.functor.map
      ((scalarExceptionalBeta l D.k (hcd := BaseFieldFiniteCD.of_isAlgClosed l D.k)
          (quotient l E h) ha (X := X) (Y := S)
          (f := Over.homMk X.hom (by simp [S]))
          c (R m) (R n)).app (coefficientUnit l E D enc hU m)).hom ≫
    (enc n X.left).fixedDerived.functor.map ((R n).upper.map us).hom

/-- Equality of the internal compact-support scalar map with the transported etale map.
The input is any bounded constructible finite-Tor etale complex L, together with any
internal Dctf realization K and an isomorphism from its fixed-module encoding to nu* L.
The equation includes the compact-support site and scalar/site comparisons explicitly.
Source: clause (b) of the finite-stage identification
(blueprint: lem-coef-finite-dualizing-condensed-agreement). -/
def compactScalarAgreement {m n : ℕ} (h : n ≤ m)
    (s : ∀ T : Scheme.{u}, ScalarCoordinates l E h T (enc m T) (enc n T))
    (L : DerivedCategory.Plus
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))))
    (K : ConstantModelConstructibleFiniteTor (ring l E m).X X.left)
    (e : (enc m X.left).fixedDerived.functor.obj K.obj ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) X.left).mapDerivedCategory.obj L.obj)
    (hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (finiteDualizingQuotient l E h) X.left).obj L.obj)) : Prop :=
  (enc n (Spec (.of D.k))).fixedDerived.functor.map
        ((scalarCompactSupportMap (quotient l E h) c.i c.g).app K.obj) ≫
      (supportEncoding l E n c (enc n)).hom.app
        ((scalarSixChange (quotient l E h) X.left).obj K.obj) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).map
          ((s X.left).extension.hom.app K.obj ≫
            (pbcFixedScalarExtension (Scheme.ProEt.topology X.left)
              (finiteDualizingQuotient l E h)).map e.hom ≫
            (pbcComparisonReduction X.left (finiteDualizingQuotient l E h)).hom.app L.obj) =
    (s (Spec (.of D.k))).extension.hom.app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (ring l E m).X c).obj K.obj) ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology (Spec (.of D.k)))
        (finiteDualizingQuotient l E h)).map
          ((supportEncoding l E m c (enc m)).hom.app K.obj ≫
            (ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c).map e.hom ≫
            (ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E m) c).hom.app L) ≫
      (pbcComparisonReduction (Spec (.of D.k)) (finiteDualizingQuotient l E h)).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c).obj L.obj) ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
        (Spec (.of D.k))).mapDerivedCategory.map
          (Etale.ExceptionalCoefficients.compactSupportMap
            (finiteDualizingQuotient l E h) c L.obj) ≫
      (ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n) c).inv.app
        ⟨(Etale.scalarExtension (finiteDualizingQuotient l E h) X.left).obj L.obj, hLB⟩

/-- The finite condensed and transported dualizing objects agree by their specified
counits, and this unique isomorphism commutes with the actual coefficient comparisons.
The auxiliary existential witnesses certify the positive quotient is listed, normalize
its scalar encoding, and certify membership of the regular unit in Dctf; none is an
extra hypothesis.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
prop-coef-integral-dualizing.proof.md, first paragraph
(blueprint: lem-coef-finite-dualizing-condensed-agreement).

Proof: The algebraically closed geometric field has finite ell-cohomological dimension.
The regular coefficient unit is finite free in degree zero, and each positive quotient
is finite ell-primary. The finite-discrete section-action encodings identify units,
constructibility, Tor intervals, and the compactification's open and proper factors.
Restriction along each quotient is the identity on additive sections; adjunction
uniqueness then gives the normalized scalar-extension comparison. Thus the unit is
Dctf, and preservation for the given localizing right adjoint and the comparison-class
exceptional functor puts both dualizing objects in Dctf. Their specified counits represent
the same compact-support Hom functor on that full category. Transposing each counit
through the other bijection gives inverse maps; injectivity gives uniqueness and the
counit equation. The normalized section-scalar adjunction identifies the internal
proper scalar mate with the ordinary proper counit mate, and the open comparison with
the ordinary extension-by-zero scalar comparison. Constructible pro-etale complexes
have bounded etale origins with the same finite Tor intervals. The etale/pro-etale
coefficient compatibility square therefore identifies this proper/open composite with
the transported etale comparison, proving (b). Both the internal beta and the etale
finite dualizing reduction are defined by transposing the scalar extension of the
same counit after the inverse compact-support scalar map. Naturality of that map and
the defining equation for phi give equal counit transposes for the two sides of (c).
Their common source is Dctf by scalar preservation, so the comparison-class Hom bijection
is injective there and gives the required equality. The cited scalar-exceptional and
finite-dualizing comparison results make both reduction maps isomorphisms. -/
theorem finiteDualizingCondensedAgreement :
    ∃ (ha : ∀ (m n : ℕ) (h : n ≤ m), ListedCoefficientMap l (quotient l E h))
      (s : ∀ (m n : ℕ) (h : n ≤ m) (T : Scheme.{u}),
        ScalarCoordinates l E h T (enc m T) (enc n T))
      (hU : ∀ n : ℕ,
        (constantModelBoundedConstructible (ring l E n).X (Spec (.of D.k)) ⊓
          DerivedCategory.finiteTorAmplitude _)
            (unit l E n (Spec (.of D.k)) (enc n (Spec (.of D.k)))))
      (φ : ∀ n : ℕ,
        condensed l E D X c enc R hU n ⟶ transported l E D X c n),
      (∀ n : ℕ,
        ordinaryCtf (Padic.coefficientExtensionRing l E (n + 1)) X.left
            (condensed l E D X c enc R hU n) ∧
        ordinaryCtf (Padic.coefficientExtensionRing l E (n + 1)) X.left
            (transported l E D X c n) ∧
        IsIso (φ n) ∧
        (ProEtale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).map (φ n) ≫
          transportedCounit l E D X c n = condensedCounit l E D X c enc R hU n ∧
        ∀ ψ : condensed l E D X c enc R hU n ⟶ transported l E D X c n,
          (ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).map ψ ≫
            transportedCounit l E D X c n = condensedCounit l E D X c enc R hU n →
          ψ = φ n) ∧
      (∀ (m n : ℕ) (h : n ≤ m)
          (L : DerivedCategory.Plus
            (Sheaf X.left.smallEtaleTopology
              (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))))
          (_hL : (Etale.DerivedCategory.isBoundedConstructible
            (finiteDualizingCoeff l E m) X.left ⊓ DerivedCategory.finiteTorAmplitude _) L.obj),
        ∃ hLB : DerivedCategory.TStructure.t.plus
            ((Etale.scalarExtension (finiteDualizingQuotient l E h) X.left).obj L.obj),
          ∀ (K : ConstantModelConstructibleFiniteTor (ring l E m).X X.left)
            (e : (enc m X.left).fixedDerived.functor.obj K.obj ≅
              (ProEtale.comparisonUpperStar
                (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
                  X.left).mapDerivedCategory.obj L.obj),
            compactScalarAgreement l E D X c enc h (s m n h) L K e hLB) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        IsIso (condensedReduction l E D X c enc R hU h (ha m n h)
          (s m n h X.left) (s m n h (Spec (.of D.k)))) ∧
        IsIso (transportedReduction l E D X c h) ∧
        (pbcFixedScalarExtension (Scheme.ProEt.topology X.left)
            (finiteDualizingQuotient l E h)).map (φ m) ≫
          transportedReduction l E D X c h =
        condensedReduction l E D X c enc R hU h (ha m n h)
            (s m n h X.left) (s m n h (Spec (.of D.k))) ≫ φ n) := by
  sorry

end WeilConjectures.FiniteCondensedDualizing
