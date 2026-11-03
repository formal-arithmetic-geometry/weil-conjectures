/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.CondensedCoefficientDualOnX
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedBasicOperationsCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.ScalarChangeAdjunctions
public import WeilConjectures.CategoryTheory.Monoidal.Closed.PairingComparison

/-! # Canonical comparison maps for finite Poincare reduction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
`thm-pod-finite-reduction.md` and its proof (blueprint: thm-pod-finite-reduction).

The sections comparison is the scalar-adjunction mate of the sheaf scalar unit.
Its restriction square is normalized to the identity on actual sections. Tate-line
coordinates retain their coefficient-unit and balanced-tensor normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.PoincareFiniteReduction

variable {A B : ScalarSixRing.{u}} (a : A ⟶ B)
  (k : Type u) [Field k] [IsAlgClosed k]
  (φ : condensedScalarRing A.X →+* condensedScalarRing B.X)

/-- The restriction square for actual scalar sections. Its normalization below
requires the identity on every section, so it contains no free scalar automorphism.
Source: blueprint proof, the unit-adjunct eta (blueprint: thm-pod-finite-reduction). -/
abbrev RestrictionSquare :=
  Mod.comap (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom (Spec (.of k))) ⋙
      CohomologyTransport.sections A.X (Spec (.of k)) ≅
    CohomologyTransport.sections B.X (Spec (.of k)) ⋙ ModuleCat.restrictScalars φ

/-- Localize the exact restriction square using the canonical exact-functor factors.
Source: blueprint proof, naturality of eta (blueprint: thm-pod-finite-reduction). -/
def derivedRestrictionSquare (σ : RestrictionSquare a k φ) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso σ ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The specified point comparison: transpose sections of the native sheaf unit
under the normalized ordinary scalar adjunction. No isomorphism is assumed.
Source: blueprint proof, eta_N (blueprint: thm-pod-finite-reduction). -/
def pointComparison (σ : RestrictionSquare a k φ)
    (N : DerivedCategory (ModuleRingedComparison.internalModules A.X (Spec (.of k)))) :
    (ModuleCat.ordinaryDerivedExtendScalars φ).obj
        ((CohomologyTransport.sections A.X (Spec (.of k))).mapDerivedCategory.obj N) ⟶
      (CohomologyTransport.sections B.X (Spec (.of k))).mapDerivedCategory.obj
        ((scalarSixChange a (Spec (.of k))).obj N) :=
  ((AlgebraicGeometry.Etale.scalarChangePointAdjunction φ).homEquiv _ _).symm
    ((CohomologyTransport.sections A.X (Spec (.of k))).mapDerivedCategory.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom (Spec (.of k)))).unit.app N) ≫
      (derivedRestrictionSquare a k φ σ).hom.app ((scalarSixChange a (Spec (.of k))).obj N))

/-- Change only the selected positive coefficient exponent, retaining the setting.
Source: A_n and A_m of the statement (blueprint: thm-pod-finite-reduction). -/
def atLevel (P : CondensedPoincareDualityConventions.{u}) (n : ℕ) :
    CondensedPoincareDualityConventions.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_le_succ (Nat.zero_le n) }

/-- The finite coefficient presentation at exponent n+1.
Source: the displayed finite rings (blueprint: thm-pod-finite-reduction). -/
abbrev coefficient (P : CondensedPoincareDualityConventions.{u}) (n : ℕ) :
    Coefficient P.ell :=
  .finite (.of (Padic.coefficientExtensionRing P.ell P.extension (n + 1)))
    (Padic.finite_coefficientExtensionRing P.ell P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))) n
    (by simpa only [Nat.cast_pow] using coefficientFiniteTwist_annihilator P.ell P.extension n)

/-- The actual quotient map, on continuous finite-valued sections, with the discrete
coefficient topology used by the finite presentation.
Source: canonical finite coefficient change (blueprint: thm-pod-finite-reduction). -/
def ringMap (P : CondensedPoincareDualityConventions.{u}) {n m : ℕ} (h : m ≤ n) :
    (coefficient P n).ring P.ell ⟶ (coefficient P m).ring P.ell := by
  let R := Padic.coefficientExtensionRing P.ell P.extension (n + 1)
  let S := Padic.coefficientExtensionRing P.ell P.extension (m + 1)
  letI : TopologicalSpace R := ⊥
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  letI : DiscreteTopology S := discreteTopology_bot S
  exact Profinite.continuousMapRingSheafMap
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
    (continuous_of_discreteTopology)

/-- Bundle that quotient as a commutative condensed coefficient map.
Source: native coefficient change (blueprint: thm-pod-finite-reduction). -/
def change (P : CondensedPoincareDualityConventions.{u}) {n m : ℕ} (h : m ≤ n) :
    (coefficient P n).bundled.{u} P.ell ⟶ (coefficient P m).bundled P.ell :=
  ⟨⟨(sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (ringMap P h)⟩⟩

/-- The same quotient map on the actual scalar rings Lambda(*).
Source: point coefficient identification (blueprint: thm-pod-finite-reduction). -/
def scalarMap (P : CondensedPoincareDualityConventions.{u}) {n m : ℕ} (h : m ≤ n) :
    condensedScalarRing ((coefficient P n).obj P.ell) →+*
      condensedScalarRing ((coefficient P m).obj P.ell) :=
  ((InternalAbelianSheafModule.sectionScalarMap (coherentTopology Profinite.{u})
    (R := (coefficient P n).obj P.ell) (S := (coefficient P m).obj P.ell)
    (change P h).hom.hom).hom.app (.op (⊤_ Profinite.{u}))).hom

/-- Transport the normalized Tate-line map through the two identity-scalar unitors.
Source: blueprint proof, dual/twist comparison (blueprint: thm-pod-finite-reduction). -/
def traceLineComparison (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (d : ℕ)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (p : ScalarLineCoordinates ell a ha X) :
    (scalarSixChange a X).obj
        (smoothTraceCoefficientLine ell (c.bundled ell) c (Iso.refl _) X d) ⟶
      smoothTraceCoefficientLine ell (c'.bundled ell) c' (Iso.refl _) X d :=
  (scalarSixChange a X).map ((scalarChangeUnit (c.bundled ell) X).hom.app _) ≫
    scalarLineZero ell a X d (p.power d) ≫
    (scalarChangeUnit (c'.bundled ell) X).inv.app _

/-- Scalar comparison of the coefficient dual tensored with the positive Tate line.
The dual arrow is the internal-Hom comparison followed by the scalar unit map.
Source: blueprint proof, Step 1 (blueprint: thm-pod-finite-reduction). -/
def twistedDualComparison (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u}) (d : ℕ)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (p : ScalarLineCoordinates ell a ha X) (K : c.derived ell X) :=
  letI := scalarSixChangeMonoidal a X
  (scalarSixTensorIso a X _ _).hom ≫
    (unitDualComparison (scalarSixChange a X) (𝟙 ((scalarSixChange a X).obj K))
      (Functor.OplaxMonoidal.η (scalarSixChange a X)) ⊗ₘ
        traceLineComparison ell a X d ha p)

/-- The explicit pairing-reduction formula at a specified coefficient arrow.
This definition asserts no theorem for arbitrary arrows. It names the unchanged
existence, normalization, pairing-identity and inverse-square formula so that its
finite-ring specialization does not repeatedly expand coefficient constructions.
Source: the statement and assembly proof (blueprint: thm-pod-finite-reduction). -/
def PairingReduction (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (cn cm : Coefficient ell)
    (a : cn.bundled.{u} ell ⟶ cm.bundled ell)
    (φ : condensedScalarRing (cn.obj ell) →+* condensedScalarRing (cm.obj ell))
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor (cn.obj ell) X.left)
    (hK : IsPerfectOnCoefficientSite (cn.obj ell) X.left K.obj) : Prop :=
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let T := ModuleCat.ordinaryDerivedExtendScalars φ
    let Km := (scalarSixChange a X.left).obj K.obj
    ∃ (hKm : constantModelBoundedConstructible (cm.obj ell) X.left Km ∧
        DerivedCategory.finiteTorAmplitude _ Km)
      (hPKm : IsPerfectOnCoefficientSite (cm.obj ell) X.left Km),
    ∃ (σ : RestrictionSquare a D.k φ),
    (∀ (M : ModuleRingedComparison.internalModules (cm.obj ell) (Spec (.of D.k)))
      (x : (CohomologyTransport.sections (cm.obj ell) (Spec (.of D.k))).obj M),
      (σ.hom.app M).hom x = x) ∧
    ∃ (ha : cn.integralMap ell ≫ a.hom.hom = cm.integralMap ell)
      (p : ScalarLineCoordinates ell a ha X.left),
    let Cn := (pairingCompactSections (cn.obj ell) D.k cf).obj K.obj
    let u := compactComparison a D.k φ σ cf K.obj
    let v := ordinaryTwistedComparison ell a D.k φ σ X.hom
      d ha p K.obj
    let βn := derivedPoincarePairing ell D hEll (cn.bundled ell)
      cn (Iso.refl _) X d cf K hK
    let βm := derivedPoincarePairing ell D hEll (cm.bundled ell)
      cm (Iso.refl _) X d cf ⟨Km, hKm⟩ hPKm
    ∃ (hu : IsIso u) (hn : IsIso (curry βn)) (hm : IsIso (curry βm)),
    letI := hu
    letI := hn
    letI := hm
    let w := unitDualComparison T (inv u) (Functor.OplaxMonoidal.η T)
    IsIso w ∧ IsIso v ∧
      (Functor.LaxMonoidal.μ T Cn _ ≫ T.map βn ≫ Functor.OplaxMonoidal.η T =
        (u ⊗ₘ v) ≫ βm) ∧
      (T.map (inv (curry βn)) ≫ v = w ≫ inv (curry βm))

end WeilConjectures.PoincareFiniteReduction
