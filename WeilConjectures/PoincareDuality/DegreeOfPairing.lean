/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.PoincareDuality.GlobalTwistInterchange.GlobalTwistInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
public import WeilConjectures.AlgebraicGeometry.Native.NativeSignedLine
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupProper.CondensedProperComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.CondensedPoincareSetting
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Degree of the Poincare pairing

Source: latest blueprint, `prop-pod-degree-of-the-pairing.md` and its proof,
complementary-degree component and elimination of the invertible point twist
(blueprint: prop-pod-degree-of-the-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000]
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct

namespace WeilConjectures.PoincareDuality

variable (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u})
  (c : PurityTransport.Coefficient ell) (e : c.bundled.{u} ell ≅ Λ)

/-- Hom from the regular derived scalar unit is the cohomology group.
Source: complementary-degree groups (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev PairingCohomology (P : DerivedCategory
    (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) (i : ℤ) := 𝟙_ _ ⟶ P⟦i⟧

/-- The shift convention H^(-i)(Q[2d]) = H^(2d-i)(Q), with its actual
canonical shift-addition map, rather than an equality of unrelated group types.
Source: first proof step (blueprint: prop-pod-degree-of-the-pairing). -/
def complementaryShift (Q : DerivedCategory
    (ModuleCat.{u + 1} (condensedScalarRing Λ.X))) (d i : ℤ) :
    Q⟦(2 * d - i)⟧ ≅ (Q⟦(2 * d)⟧) ⟦(-i)⟧ :=
  (shiftFunctorAdd' _ (2 * d) (-i) (2 * d - i) rfl).app Q

/-- The scalar of the degree-zero component, using the existing tensor-shift
comparison, its total-complex signs, H^0 of the unit and evaluation at 1.
Source: first displayed pairing (blueprint: prop-pod-degree-of-the-pairing). -/
def degreewisePoincareValue
    {P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X))} (d i : ℤ)
    (β : P ⊗ Q⟦2 * d⟧ ⟶ 𝟙_ _)
    (x : PairingCohomology Λ P i) (y : PairingCohomology Λ Q (2 * d - i)) :
    condensedScalarRing Λ.X :=
  identificationScalarValue
    (identificationDegreeValue β i x (y ≫ (complementaryShift Λ Q d i).hom))

/-- The genuine root-tower Tate power in the given coefficient coordinates.
Its degree-zero derived realization is smoothTraceCoefficientLine.
Source: native Tate twists (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingPointLine (T : Scheme.{u}) (d : ℕ) :=
  (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := Λ.X)
    e.hom.hom.hom T)).obj (c.line ell T d)

/-- Canonical exact scalar-extension/single comparison for the native Tate line.
The extension is exact because the coefficient change is an isomorphism.
Source: twist definition (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingLineSingleIso (T : Scheme.{u}) (d : ℕ) :
    smoothTraceCoefficientLine ell Λ c e T d ≅
      (DerivedCategory.singleFunctor _ 0).obj (pairingPointLine ell Λ c e T d) := by
  let a := coefficientMap (Λ := c.obj ell) (Λ' := Λ.X) e.hom.hom.hom T
  have : IsIso a := by dsimp [a, coefficientMap]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv a).symm
  exact (Mod.extendScalars a).singleFunctorCompLeftDerivedFunctorIso.app _

/-- The unit comparison for the exact inverse image, built from the ordinary
cartesian regular-module map and the canonical single-complex comparisons.
Source: cartesian coefficients (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingPullUnitIso {T S : Scheme.{u}} (f : T ⟶ S) :
    (scalarSixPull Λ f).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (scalarSixPull Λ f).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((upperStar Λ.X f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (upperStarObjRegularIso Λ.X f) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- A point-line section as a map from the derived regular unit, using the
published terminal-section equivalence and the exact scalar-extension comparison.
Source: point-line sections (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingLineSection (S : Scheme.{u}) (d : ℕ)
    (z : (CohomologyTransport.sections Λ.X S).obj (pairingPointLine ell Λ c e S d)) :
    𝟙_ _ ⟶ smoothTraceCoefficientLine ell Λ c e S d :=
  (DerivedCategory.singleFunctorObjUnitIso _).inv ≫
    (DerivedCategory.singleFunctor _ 0).map
      (GlobalTwistInterchange.sectionArrow Λ.X S (pairingPointLine ell Λ c e S d) z) ≫
    (pairingLineSingleIso ell Λ c e S d).inv

/-- The signed inverse of the positive point line, using the recorded signed
coefficient convention. Taking exponent -1 of Lambda(d) is Lambda(-d).
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInversePointLine (S : Scheme.{u}) (d : ℕ) :=
  coefficientSignedTwist S (condensedRingObj Λ.X S) (pairingPointLine ell Λ c e S d) (-1)

/-- The actual inverse twist in the derived category, using the recorded
coefficientTwistFunctor applied to the regular unit.
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInverseComplex (S : Scheme.{u}) (d : ℕ) :=
  (coefficientTwistFunctor S (condensedRingObj Λ.X S)
    (pairingPointLine ell Λ c e S d) (-1)).obj (𝟙_ _)

/-- The unit comparison between the recorded inverse twisting functor at the
unit and its actual ordinary inverse line in degree zero.
Source: inverse Tate twist (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseRealization (S : Scheme.{u}) (d : ℕ) :
    pairingInverseComplex ell Λ c e S d ≅
      (DerivedCategory.singleFunctor _ 0).obj (pairingInversePointLine ell Λ c e S d) :=
  λ_ _

/-- Lambda(-d) is H^0 of the actual negative point twist after exact scalar sections.
Source: inverse point line (blueprint: prop-pod-degree-of-the-pairing). -/
abbrev pairingInverseSections (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) 0).obj
    ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategory.obj
      (pairingInverseComplex ell Λ c e (Spec (.of k)) d))

/-- Exact scalar sections and the single-complex comparison read a class of
Lambda(-d) as an ordinary section of the inverse point line.
Source: inverse-line sections (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseSectionValue (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ) :
    pairingInverseSections ell Λ c e k d ⟶
      (CohomologyTransport.sections Λ.X (Spec (.of k))).obj
        (pairingInversePointLine ell Λ c e (Spec (.of k)) d) :=
  (DerivedCategory.homologyFunctor _ 0).map
    ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategory.map
      (pairingInverseRealization ell Λ c e (Spec (.of k)) d).hom ≫
      ((CohomologyTransport.sections Λ.X (Spec (.of k))).mapDerivedCategorySingleFunctor
        0).hom.app _) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _

/-- Canonical evaluation of the actual inverse twist against the positive line.
The signed convention uses Hom(unit tensor L,unit); its left unitor inserts L
in that evaluation. Exact point sections and H^0 read the resulting scalar.
Source: tensor--Hom untwisting (blueprint: prop-pod-degree-of-the-pairing). -/
def pairingInverseEvaluation (k : Type u) [Field k] [IsAlgClosed k] (d : ℕ)
    (v : pairingInverseSections ell Λ c e k d)
    (z : (CohomologyTransport.sections Λ.X (Spec (.of k))).obj
      (pairingPointLine ell Λ c e (Spec (.of k)) d)) : condensedScalarRing Λ.X :=
  let S := Spec (.of k)
  let L := pairingPointLine ell Λ c e S d
  let V := pairingInversePointLine ell Λ c e S d
  let ε := (λ_ (𝟙_ _)).inv ≫
    ((GlobalTwistInterchange.sectionArrow Λ.X S L z ≫ (λ_ L).inv) ⊗ₘ
      GlobalTwistInterchange.sectionArrow Λ.X S V
        ((pairingInverseSectionValue ell Λ c e k d).hom v)) ≫
    (ihom.ev (𝟙_ _ ⊗ L)).app (𝟙_ _)
  identificationScalarValue
    ((pairingExactScalarPointCup_unitIso Λ.X k).hom ≫
      (CohomologyTransport.sections Λ.X S).mapDerivedCategory.map
        ((DerivedCategory.singleFunctorObjUnitIso _).inv ≫
          (DerivedCategory.singleFunctor _ 0).map ε ≫
          (DerivedCategory.singleFunctorObjUnitIso _).hom) ≫
      (pairingExactScalarPointCup_unitIso Λ.X k).inv)

end WeilConjectures.PoincareDuality
