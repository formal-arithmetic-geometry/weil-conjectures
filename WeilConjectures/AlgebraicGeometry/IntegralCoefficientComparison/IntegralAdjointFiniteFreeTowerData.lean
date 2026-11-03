/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist

/-! # Coefficient coordinates for the reconstructed integral adjoint

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1)--(2).
The coefficient map is postcomposition by the given inclusion of fields, restricted
 to their valuation rings. The tower scalar models below are the existing exact
whole-system scalar models; no unrelated functor is a parameter.
(blueprint: def-pur-integral-adjoint-coefficient-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
open IntegralDirectImageTower CurrentNativeIntegralTower
open CondensedRing

variable (ell : ℕ) [Fact ell.Prime]

/-- Bundle the recorded continuous integer ring, retaining its multiplication.
Source: paragraph (1), O_E (blueprint: def-pur-integral-adjoint-coefficient-data). -/
abbrev ring (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] : ScalarSixRing.{u} := ⟨spIntegralCondensed ell E⟩

/-- Commutativity of the existing pulled-back coefficient ring.
Source: coefficient convention (blueprint: def-pur-integral-adjoint-coefficient-data). -/
instance ringAtComm (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (T : Scheme.{u}) :
    IsCommMonObj (condensedRingObj (ring ell E).X T) := by
  change IsCommMonObj (condensedRingObj (spIntegralCondensed ell E) T)
  infer_instance

variable (E F : Type u) [Field E] [Field F]
  [Algebra (Padic ell) E] [Algebra (Padic ell) F]
  [FiniteDimensional (Padic ell) E] [FiniteDimensional (Padic ell) F]
  (i : E →ₐ[Padic ell] F)

/-- The restriction of the field inclusion is continuous for the spectral topologies.
Source: finite-extension absolute-value uniqueness, paragraph (1)
(blueprint: def-pur-integral-adjoint-coefficient-data).
Proof: uniqueness of the extending absolute value identifies the absolute value of
 i(x) with that of x. Thus the inclusion of fields is an isometry. Restrict its
continuous map to the valuation subrings. -/
theorem integerInclusion_continuous :
    letI := spectralNorm.normedField (Padic ell) E
    letI := spectralNorm.normedField (Padic ell) F
    Continuous (WeilConjectures.integralScalarIntegerInclusion ell E F i) := by
  sorry

/-- The actual condensed map O_E -> O_F; it sends a continuous section s to i ∘ s.
Source: paragraph (1), field inclusion
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
def map : ring ell E ⟶ ring ell F :=
  letI := spectralNorm.normedField (Padic ell) E
  letI := spectralNorm.normedField (Padic ell) F
  ⟨⟨twistContinuousMap
    (WeilConjectures.integralScalarIntegerInclusion ell E F i)
    (integerInclusion_continuous ell E F i)⟩⟩

/-- Identity postcomposition is the identity coefficient map.
Source: paragraph (2), identity coefficient change
(blueprint: def-pur-integral-adjoint-coefficient-data).
Proof: evaluate on a profinite object and then on a point. Both maps send s(x) to s(x). -/
theorem map_id : map ell E E (AlgHom.id (Padic ell) E) = 𝟙 (ring ell E) := by
  sorry

/-- Successive postcompositions are postcomposition by the composite inclusion.
Source: paragraph (2), successive coefficient changes
(blueprint: def-pur-integral-adjoint-coefficient-data).
Proof: evaluate on a continuous function and a point. Both sides send s(x) to j(i(s(x))). -/
theorem map_comp (L : Type u) [Field L] [Algebra (Padic ell) L]
    [FiniteDimensional (Padic ell) L] (j : F →ₐ[Padic ell] L) :
    map ell E F i ≫ map ell F L j = map ell E L (j.comp i) := by
  sorry

/-- Native derived scalar extension along the actual field inclusion.
Source: paragraph (1), S_T (blueprint: def-pur-integral-adjoint-coefficient-data). -/
abbrev scalar (T : Scheme.{u}) := scalarSixChange (map ell E F i) T

/-- The canonical scalar unitor, including the identity coefficient-map transport.
Source: paragraph (2), E=F (blueprint: def-pur-integral-adjoint-coefficient-data). -/
def scalarId (T : Scheme.{u}) : scalar ell E E (AlgHom.id (Padic ell) E) T ≅
    𝟭 (Integral ell E T) :=
  eqToIso (congrArg (fun a ↦ scalarSixChange a T) (map_id ell E)) ≪≫
    scalarChangeUnit (ring ell E) T

/-- The canonical derived scalar associator, with its actual composite ring map.
Source: paragraph (2), E ⊂ F ⊂ L
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
def scalarComp (L : Type u) [Field L] [Algebra (Padic ell) L]
    [FiniteDimensional (Padic ell) L] (j : F →ₐ[Padic ell] L) (T : Scheme.{u}) :
    scalar ell E F i T ⋙ scalar ell F L j T ≅ scalar ell E L (j.comp i) T :=
  scalarSixTower (map ell E F i) (map ell F L j) T ≪≫
    eqToIso (congrArg (fun a ↦ scalarSixChange a T) (map_comp ell E F i L j))

/-- An actual supplied tower adjunction, and its specified integral realization.
The left functor is the compactification tower functor. The right native functor
 is definitionally reduction, this tower right adjoint, and total derived limit.
Source: integral-edge statement
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
structure Edge (s : Presentation ell E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  support_closed : ∀ M : Towers ell E s X,
    spConstructibleTorTowers ell E Y (s.towers Y) ((towerShriek ell E s c).obj M.obj)
  right : Towers ell E s Y ⥤ Towers ell E s X
  towerAdjunction : towerSupport ell E s c support_closed ⊣ right
  coordinates : CurrentNativeIntegralTower.Coordinates ell E s
  levels : SpTowerGluing.Levels ell E s.base s.operations
    (coordinates.calculus ell E s) c support_closed right towerAdjunction
  integral : CurrentNativeIntegralTower.IntegralEdge ell E s c support_closed right towerAdjunction

variable {ell E} in
/-- The native integral compact-support restriction.
Source: integral-edge statement (blueprint: def-pur-integral-adjoint-coefficient-data). -/
abbrev Edge.P {s : Presentation ell E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (e : Edge ell E s c) := support ell E c e.integral.supportClosed

variable {ell E} in
/-- H = L_X J red_Y, on Dbc and with the actual total-limit data.
Source: integral-edge statement (blueprint: def-pur-integral-adjoint-coefficient-data). -/
abbrev Edge.H {s : Presentation ell E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} (e : Edge ell E s c) :=
  CurrentNativeIntegralTower.right ell E s e.integral.limitX e.integral.reductionY
    e.right e.integral.closed

/-- The native inclusion in section-ring coordinates.
Source: paragraph (1), independent coefficient pullbacks
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
abbrev sectionMap (T : Scheme.{u}) :=
  CondensedRing.sectionRingMap T (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)

/-- Exact restriction commutes with the recorded internal/section equivalences.
Source: paragraph (1), coefficient presentation
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
def sectionRestriction (T : Scheme.{u}) :
    (Mod.comap (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).mapDerivedCategory ⋙
        (sectionEquivalence ell E T).functor ≅
      (sectionEquivalence ell F T).functor ⋙
        (WeilConjectures.SemilinearSections.res (sectionMap ell E F i T)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompNatIso
    (sectionModuleComapIso T (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The canonical change-of-presentation for derived scalar extension. It is the
unique left-adjoint comparison of the exact restriction identification.
Source: paragraph (1), ordinary derived extension
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
def sectionScalar (T : Scheme.{u}) (D : SpCoefficientTowersAbelian ell E T) :
    scalar ell E F i T ⋙ (sectionEquivalence ell F T).functor ≅
      (sectionEquivalence ell E T).functor ⋙ (D.scalar (sectionMap ell E F i T)).model.T := by
  let e := sectionEquivalence ell E T
  let e' := sectionEquivalence ell F T
  let V : Integral ell F T ⥤ Integral ell E T :=
    (Mod.comap (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).mapDerivedCategory
  let W := (WeilConjectures.SemilinearSections.res
    (sectionMap ell E F i T)).mapDerivedCategory
  let rho : e'.inverse ⋙ V ≅ W ⋙ e.inverse :=
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (e'.inverse ⋙ V) e.unitIso ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft e'.inverse (sectionRestriction ell E F i T)) e.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight e'.counitIso W) e.inverse ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor W) e.inverse
  exact (((Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := spIntegralCondensed ell E)
      (Λ' := spIntegralCondensed ell F)
      (map ell E F i).hom.hom T)).comp e'.toAdjunction).ofNatIsoRight rho).leftAdjointUniq
      (e.toAdjunction.comp (D.scalar (sectionMap ell E F i T)).adjunction)

end AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
