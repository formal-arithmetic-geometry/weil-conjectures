/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.NormalizedEtaleOriginWitnesses
public import Sheaf.Paper.BoundaryDualizingComposition
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.CategoryTheory.AdjointMate
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.Paper.ConnectedTateLineEndomorphisms
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteClosedShriek
import Sheaf.CategoryTheory.FullyFaithfulCounitDescent
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.SiteClosedCounitTransport
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
import Sheaf.Paper.SfCommonStageWeilCohomology
import Sheaf.SixFunctors.CompactCoefficientComposition
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-!
# Finite exceptional dualizing comparisons

Source: blueprint order 2140, `lem-coef-finite-dualizing` (blueprint:
lem-coef-finite-dualizing).

The finite term is the specified exceptional inverse image of the regular
coefficient unit.  The transition interface below is the adjunct of the
counit-defined coefficient comparison; it is exposed separately so a strict
normalized tower must identify its transitions with these maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The published ring-sheafification witness with both universes explicit.
Source: blueprint ordinary coefficient sheaves (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The published small-site witness at the actual coefficient universe.
Source: blueprint small-site convention (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- `ω_(X,n)=Ra_n^!(A_n)_s`, with the positive level convention `n+1`.
Source: blueprint order 2140 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingFiniteTerm (D : FiniteFieldDatum.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (n : ℕ) : normalizedDVRDerived l E X n :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  ((ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
    (HasCompactification.compactification (X ↘ Spec (.of D.k)))).obj
    ((DerivedCategory.singleFunctor
      (scalarReductionTarget.{u, u} l E (Spec (.of D.k)) n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) n))))

/-- The coefficient ring in the standard fixed-scalar size presentation.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
abbrev finiteDualizingCoeff (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- The quotient before the standard coefficient-universe lift.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingQuotientBase {m n : ℕ} (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The actual quotient homomorphism at positive levels.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingQuotient {m n : ℕ} (h : n ≤ m) :
    finiteDualizingCoeff l E m →+* finiteDualizingCoeff l E n :=
  RingHom.ulift.{u + 1, u + 1} (finiteDualizingQuotientBase l E h)

/-- Identity quotient. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: both maps send the residue class of x to the residue class of x. -/
theorem finiteDualizingQuotient_id (n : ℕ) :
    finiteDualizingQuotient l E (le_refl n) = RingHom.id _ := by
  sorry

/-- Quotient composition. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: on a representative x both composites give its class in the last quotient. -/
theorem finiteDualizingQuotient_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    finiteDualizingQuotient l E (hmn.trans hrm) =
      (finiteDualizingQuotient l E hmn).comp (finiteDualizingQuotient l E hrm) := by
  sorry

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- One fixed compactification for all coefficient levels.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The ordinary etale exceptional functor whose transport is sfFiniteExceptional.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleExceptional (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) (Spec (.of D.k)) ⥤
      Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
    (X ↘ Spec (.of D.k))

/-- The ordinary etale dualizing object, at the regular coefficient unit.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleTerm (n : ℕ) :
    Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X :=
  (finiteDualizingEtaleExceptional l E D X n).obj
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The ordinary etale compact-support functor, for the same compactification.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
abbrev finiteDualizingEtaleSupport (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) (finiteDualizingCompactification D X)

/-- The actual etale exceptional adjunction, with its specified counit.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleAdjunction (n : ℕ) :
    finiteDualizingEtaleSupport l E D X n ⊣ finiteDualizingEtaleExceptional l E D X n :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) (X ↘ Spec (.of D.k))

/-- The dualizing counit, evaluated at the actual regular coefficient object.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleCounit (n : ℕ) :
    (finiteDualizingEtaleSupport l E D X n).obj (finiteDualizingEtaleTerm l E D X n) ⟶
      Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)) :=
  (finiteDualizingEtaleAdjunction l E D X n).counit.app
    (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))

/-- The coefficient comparison of lem-fix-compact-support-coefficient-change,
expressed using the published scalar functor and proper/open canonical mates.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingCompactComparison {m n : ℕ} (h : n ≤ m) :=
  Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
    (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m)

/-- The precise counit-defined map u: the inverse compact-support comparison,
coefficient extension of epsilon, and the scalar-unit comparison, transposed under
F_B adjoint G_B. The imported total inverse is used only on the isomorphism domain
asserted in finiteDualizingCoefficientComparisons below.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleComparison {m n : ℕ} (h : n ≤ m) :
    (Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
      (finiteDualizingEtaleTerm l E D X m) ⟶ finiteDualizingEtaleTerm l E D X n :=
  (finiteDualizingEtaleAdjunction l E D X n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
        (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m) ≫
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (finiteDualizingEtaleCounit l E D X m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom)

/-- The semilinear transition is the scalar-adjunction adjunct of u.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingEtaleTransition {m n : ℕ} (h : n ≤ m) :
    finiteDualizingEtaleTerm l E D X m ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (finiteDualizingQuotient l E h)).obj (finiteDualizingEtaleTerm l E D X n) :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E h))).homEquiv _ _
        (finiteDualizingEtaleComparison l E D X h)

/-- Canonical comparison-site realization in intrinsic finite coefficients.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingRealization (Y : Scheme.{u}) (n : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
    Y).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor

/-- The fixed regular coefficient sheaf has its constant generator 1.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingFixedOne (Y : Scheme.{u}) (n : ℕ) (W : Y.ProEtᵒᵖ) :
    (𝟙_ (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))).obj.obj W :=
  (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj
    (ModuleCat.of (finiteDualizingCoeff l E n)
      (finiteDualizingCoeff l E n)))).app W (1 : finiteDualizingCoeff l E n)

/-- The regular-module realization is uniquely fixed by 1 mapping to 1.
Source: blueprint order 2484, finite-duality site comparison
(blueprint: lem-coef-finite-dualizing).
Proof: the scalar sheafification unit is locally bijective. Its images of 1 locally
generate the regular module; the linear map sending 1 to 1 therefore glues uniquely.
The reverse construction on the same local generators is its inverse. -/
theorem finiteDualizingIntrinsicUnit_existsUnique (Y : Scheme.{u}) (n : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj (𝟙_ _) ≅
        SheafOfModules.unit (integralCoefficientSheaf l E Y n),
      ∀ W : Y.ProEtᵒᵖ, e.hom.val.app W
        (sfIntrinsicRealizationUnit Y (Padic.coefficientExtensionRing l E (n + 1))
          (𝟙_ _) W (finiteDualizingFixedOne l E Y n W)) =
          (1 : (integralCoefficientSheaf l E Y n).obj.obj W) := by
  sorry

/-- The canonical regular-module realization in degree zero.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicUnit (Y : Scheme.{u}) (n : ℕ) :
    (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor (scalarReductionTarget l E Y n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (sfIntrinsicDerivedEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
      (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((sfIntrinsicModuleEquivalence Y
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategorySingleFunctor
        0).app _ ≪≫
    (DerivedCategory.singleFunctor (scalarReductionTarget l E Y n) 0).mapIso
      (finiteDualizingIntrinsicUnit_existsUnique l E Y n).choose

/-- The site-unit-normalized identification of the etale and intrinsic dualizing objects.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingOrigin (n : ℕ) :
    (finiteDualizingRealization l E X n).obj (finiteDualizingEtaleTerm l E D X n) ≅
      integralDualizingFiniteTerm l E D X n :=
  letI := (finiteDualizingCompactification D X).hasCompactification
  (sfIntrinsicDerivedEquivalence X
    (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
    (Etale.boundaryDualizingComparisonIso (finiteDualizingCoeff l E n)
        (X ↘ Spec (.of D.k)) ≪≫
      (ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1))
        (finiteDualizingCompactification D X)).mapIso
          ((sfIntrinsicDerivedEquivalence (Spec (.of D.k))
            (Padic.coefficientExtensionRing l E (n + 1))).unitIso.app (𝟙_ _) ≪≫
            (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
            (Padic.coefficientExtensionRing l E (n + 1))).inverse.mapIso
              (finiteDualizingIntrinsicUnit l E (Spec (.of D.k)) n)))

/-- Constant-ring realization of a scalar homomorphism, with commutativity forgotten.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRingMap (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A) ⟶
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y B) :=
  (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ)))

/-- Actual restriction along the constant-sheaf image of the scalar homomorphism.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRes (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :=
  SheafOfModules.restrictScalars.{u + 1} (finiteDualizingIntrinsicRingMap Y φ)

/-- Additivity of the actual underlying restriction functor.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingIntrinsicRes_additive (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (finiteDualizingIntrinsicRes Y φ).Additive :=
  inferInstanceAs
    (SheafOfModules.restrictScalars.{u + 1} (finiteDualizingIntrinsicRingMap Y φ)).Additive

/-- Scalar restriction commutes with intrinsic realization, on the same scalar-unit
sections. The generic scalar parameters keep the normalization independent of the
presentation of a finite quotient. Source: blueprint order 2484
(blueprint: lem-coef-finite-dualizing).
Proof: both sides extend the same fixed scalar action along locally bijective
constant-scalar units. The identity on their generating sections extends uniquely,
and its inverse is specified by the same sections. Naturality follows on generators. -/
theorem finiteDualizingRestriction_existsUnique (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃! e : (sfIntrinsicModuleEquivalence Y B).functor ⋙
        finiteDualizingIntrinsicRes Y φ ≅
      Sheaf.restrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
        (sfIntrinsicModuleEquivalence Y A).functor,
      ∀ (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (W : Y.ProEtᵒᵖ) (x : M.obj.obj W),
        HEq ((e.hom.app M).val.app W (sfIntrinsicRealizationUnit Y B M W x))
          (sfIntrinsicRealizationUnit Y A
            ((Sheaf.restrictScalars (ProEt.topology Y)
              (RingHom.ulift.{u + 1, u + 1} φ)).obj M) W x) := by
  sorry

/-- The tower quotient restriction is restriction along the actual quotient map.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing).
Proof: consecutive tower maps are sheafifications of the quotient maps. Induction
on the distance between the levels identifies their composite with the single
quotient factor, by its value on residue representatives. Functoriality of constant
sheafification gives equality of ring maps and therefore of restriction functors. -/
theorem finiteDualizingRestriction_eq (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E Y h =
      finiteDualizingIntrinsicRes Y (finiteDualizingQuotientBase l E h) := by
  sorry

/-- Restriction keeps underlying abelian sheaves, hence is exact.
Source: blueprint coefficient restriction, Stacks 03DA
(blueprint: lem-coef-finite-dualizing).
Proof: kernels are the same sectionwise kernels with restricted action; cokernels
are the same sheafified abelian cokernels. Their scalar actions are precomposed with
phi. Thus this additive functor preserves kernels and cokernels, hence finite limits
and finite colimits. No flatness or characteristic hypothesis is used. -/
theorem finiteDualizingGenericRestriction_exact (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (finiteDualizingIntrinsicRes Y φ) ∧
      PreservesFiniteColimits (finiteDualizingIntrinsicRes Y φ) := by
  sorry

/-- Finite-limit preservation from exact scalar restriction.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingGenericRestriction_limits (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (finiteDualizingIntrinsicRes Y φ) :=
  (finiteDualizingGenericRestriction_exact Y φ).1

/-- Finite-colimit preservation from exact scalar restriction.
Source: blueprint coefficient restriction (blueprint: lem-coef-finite-dualizing). -/
instance finiteDualizingGenericRestriction_colimits (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteColimits (finiteDualizingIntrinsicRes Y φ) :=
  (finiteDualizingGenericRestriction_exact Y φ).2

/-- Derive the scalar-unit-normalized comparison before specializing the coefficients.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingGenericDerivedRestriction (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    (sfIntrinsicDerivedEquivalence Y B).functor ⋙
        (finiteDualizingIntrinsicRes Y φ).mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (RingHom.ulift.{u + 1, u + 1} φ) ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  letI := (finiteDualizingGenericRestriction_exact Y φ).1
  letI := (finiteDualizingGenericRestriction_exact Y φ).2
  letI := sfIntrinsicModuleEquivalence_functor_additive B Y
  letI := sfIntrinsicModuleEquivalence_functor_additive A Y
  Functor.mapDerivedCategorySquareIso (finiteDualizingRestriction_existsUnique Y φ).choose

/-- The derived comparison is uniquely fixed by the generic section normalization.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing).
Proof: finiteDualizingRestriction_eq identifies the actual tower restriction with
restriction along the single quotient. Exact functor localization respects this
equality, by mapDerivedCategoryNatIso applied to eqToIso. Transport the generic
section-normalized comparison along that equality. It has the displayed HEq, and
any two isomorphisms with that HEq are equal. Thus the theorem determines the
isomorphism itself, including its components, with no choice of automorphism. -/
theorem finiteDualizingIntrinsicRestriction_existsUnique
    (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    ∃! e :
    (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (finiteDualizingQuotient l E h) ⋙
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor,
      HEq e (finiteDualizingGenericDerivedRestriction Y
        (finiteDualizingQuotientBase l E h)) := by
  sorry

/-- Exact localization of the section-normalized restriction comparison. Its unique
characterization fixes all components to the generic derived comparison.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingIntrinsicRestriction (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars (ProEt.topology Y) (finiteDualizingQuotient l E h) ⋙
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor :=
  (finiteDualizingIntrinsicRestriction_existsUnique l E Y h).choose

/-- The canonical restriction square for the full comparison-site realization.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingRealizationRestriction (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    finiteDualizingRealization l E Y n ⋙ normalizedDVRRes l E Y h ≅
      Sheaf.derivedRestrictScalars Y.smallEtaleTopology (finiteDualizingQuotient l E h) ⋙
        finiteDualizingRealization l E Y m :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingIntrinsicRestriction l E Y h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcDerivedComparisonRestrict Y (finiteDualizingQuotient l E h)) _ ≪≫
    Functor.associator _ _ _

/-- The finite transition is the actual comparison-site image of the scalar adjunct
of the counit-defined u, conjugated by the normalized dualizing origins.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingExceptionalTransition (_hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    integralDualizingFiniteTerm l E D X m ⟶
      (normalizedDVRRes l E X h).obj (integralDualizingFiniteTerm l E D X n) :=
  (finiteDualizingOrigin l E D X m).inv ≫
    (finiteDualizingRealization l E X m).map (finiteDualizingEtaleTransition l E D X h) ≫
    (finiteDualizingRealizationRestriction l E X h).inv.app
      (finiteDualizingEtaleTerm l E D X n) ≫
    (normalizedDVRRes l E X h).map (finiteDualizingOrigin l E D X n).hom

/-- Derived extension exists for the actual finite quotient restriction.
Source: blueprint order 2484, derived coefficient extension
(blueprint: lem-coef-finite-dualizing).
Proof: apply derived change of rings on the same small ringed site to the actual
quotient. K-flat resolutions compute the left adjoint, and exact restriction gives
its right adjoint. The universal property fixes the derived adjunction. -/
@[instance]
theorem finiteDualizingRestriction_isRightAdjoint
    (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRRes l E Y h).IsRightAdjoint := by
  sorry

/-- Actual derived finite extension, fixed by its adjunction to normalizedDVRRes.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def finiteDualizingExtension (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRDerived l E Y m ⥤ normalizedDVRDerived l E Y n :=
  (normalizedDVRRes l E Y h).leftAdjoint

/-- The intrinsic u is the adjunct of the specified semilinear transition. Thus its
transition is the adjunct of u under derived extension adjoint normalizedDVRRes.
Source: blueprint order 2484 (blueprint: lem-coef-finite-dualizing). -/
def integralDualizingFiniteComparison (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    (finiteDualizingExtension l E X h).obj (integralDualizingFiniteTerm l E D X m) ⟶
      integralDualizingFiniteTerm l E D X n :=
  ((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _).symm
    (integralDualizingExceptionalTransition l E D X hl h)

/-- Finite dualizing coefficient change, with the actual counit, quotient cocycle,
identity, and finite pro-etale realization. Natural level n means exponent n+1.
Source: current blueprint order 2484, lem-coef-finite-dualizing and its proof
(blueprint: lem-coef-finite-dualizing).
Proof:
1. The structure morphism is compactifiable by Nagata over the Noetherian field.
The ordinary etale exceptional adjunction gives the specified counit at A_s.
2. The regular constant object has Tor amplitude [0,0]. Verdier preservation on
strata implies that its exceptional dual is bounded constructible of finite Tor
amplitude. Consequently the compact-support coefficient comparison applies there.
Its proper/open mate is the published comparison of lem-fix-compact-support-coefficient-change.
3. Transpose its inverse followed by extension of epsilon and the regular scalar-unit
isomorphism. This is exactly finiteDualizingEtaleComparison; the adjunction triangle
identities give the displayed counit equation.
4. Localize on an affine chart and embed the chart into affine space. Composition of
adjoints identifies omega with closed exceptional image of the shifted Tate line.
Affine-space adjunction and finite closed shriek coefficient change show that this
very counit-defined map is invertible. The composite counit identity identifies the
local map with the global map, so these calculations agree on overlaps.
5. Transpose successive comparisons, use naturality, and paste the compact-support
coefficient comparisons. Their normalized scalar associator gives the cocycle;
the identity quotient and scalar-unit normalization give the unit equation.
6. The comparison-site unit identifies the etale dualizing term with the prescribed
sfFiniteExceptional term. The coefficient restriction square is normalized on scalar
sections. Transporting the scalar adjunct through these very identifications gives
integralDualizingExceptionalTransition. Conjugating the two scalar adjunctions makes
its intrinsic adjunct invertible and gives the same identity and cocycle equations.
No ambient adjunction on arbitrary pro-etale sheaves is asserted. -/
theorem finiteDualizingCoefficientComparisons (hl : l ≠ D.p) :
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (finiteDualizingCompactComparison l E D X h) ∧
      IsIso (finiteDualizingEtaleComparison l E D X h) ∧
      (finiteDualizingEtaleSupport l E D X n).map
          (finiteDualizingEtaleComparison l E D X h) ≫
        finiteDualizingEtaleCounit l E D X n =
      Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
          (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X m) ≫
        (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
          (finiteDualizingEtaleCounit l E D X m) ≫
        (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
          (Spec (.of D.k))).hom) ∧
    (∀ n : ℕ, finiteDualizingEtaleComparison l E D X (le_refl n) =
      (ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology _
        (finiteDualizingQuotient_id l E n)).hom.app (finiteDualizingEtaleTerm l E D X n)) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      (Etale.scalarExtension (finiteDualizingQuotient l E hmn) X).map
          (finiteDualizingEtaleComparison l E D X hrm) ≫
        finiteDualizingEtaleComparison l E D X hmn =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology _ _ _
        (finiteDualizingQuotient_comp l E hrm hmn)).hom.app
          (finiteDualizingEtaleTerm l E D X r) ≫
        finiteDualizingEtaleComparison l E D X (hmn.trans hrm)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      IsIso (integralDualizingFiniteComparison l E D X hl h)) ∧
    (∀ n : ℕ, integralDualizingExceptionalTransition l E D X hl (le_refl n) ≫
      (normalizedDVRResUnit l E X n).hom.app (integralDualizingFiniteTerm l E D X n) = 𝟙 _) ∧
    (∀ {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m),
      integralDualizingExceptionalTransition l E D X hl (hmn.trans hrm) ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app (integralDualizingFiniteTerm l E D X n) =
      integralDualizingExceptionalTransition l E D X hl hrm ≫
        (normalizedDVRRes l E X hrm).map
          (integralDualizingExceptionalTransition l E D X hl hmn)) := by
  sorry

end WeilConjectures
