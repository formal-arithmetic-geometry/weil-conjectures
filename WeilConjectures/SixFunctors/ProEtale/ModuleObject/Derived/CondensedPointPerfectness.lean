/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Separation
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingSummand
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarChangeModel
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteStrictPerfectHom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedFiniteTorPerfect
import Mathlib.Algebra.Module.Projective
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import Mathlib.LinearAlgebra.Contraction
import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Point perfectness of global sections

Source: latest blueprint, thm-pod-point-perfectness, clauses 1--3 and proper comparison
(blueprint: thm-pod-point-perfectness).

The coefficient objects are pulled-back condensed rings and all categories are ordinary,
uncompleted derived categories. RΓ and RΓc are the condensed coefficient complexes
recorded for def-weil-ordinary-compact-cohomology, complexes of modules over the scalar
ring Λ(*) = Γ Λ. No properness or smoothness is assumed except in the final, conditional
comparison clause.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- D(X,Λ), the ordinary unbounded derived category over the pulled-back condensed ring.
Source: def-sf-setting (blueprint: def-sf-setting). -/
abbrev sfCondensedDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The condensed finite extension field, with its canonical spectral topology.
Source: def-sf-setting (blueprint: def-sf-setting). -/
abbrev sfRationalCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj E

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The algebraic derived dual RHom_{Λ(*)}(C,Λ(*)) of a complex of Λ(*)-modules, where
Λ(*) = Γ Λ is the scalar ring of the coefficient complexes of
def-weil-ordinary-compact-cohomology.
Source: thm-pod-point-perfectness, dual convention, and def-pur-derived-internal-hom
(blueprint: def-weil-ordinary-compact-cohomology). -/
def cohomologyPointDual (C : DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ))) :=
  (ordinaryModuleDerivedInternalHom (MonObj.Γ Λ)).obj
    (op C, (DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ)))

/-- The four coefficient complexes RΓ, RΓc and their duals, indexed by compact support and
algebraic duality. RΓ and RΓc are the recorded condensed coefficient complexes
`condensedRingOrdinaryCoefficientComplex` and `condensedRingCompactCoefficientComplex`.
Source: def-weil-ordinary-compact-cohomology and thm-pod-point-perfectness, displayed list
(blueprint: def-weil-ordinary-compact-cohomology). -/
def condensedFourCohomology {X s : Scheme.{u}} {a : X ⟶ s} (c : Compactification a)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (compact dual : Bool) :
    DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ Λ)) :=
  let C := if compact then (condensedRingCompactCoefficientComplex Λ c).obj K
    else (condensedRingOrdinaryCoefficientComplex Λ a).obj K
  if dual then cohomologyPointDual Λ C else C

set_option maxHeartbeats 800000 in
-- The canonical mate elaborates several derived adjunctions in one declaration.
set_option synthInstance.maxHeartbeats 400000 in
variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ']

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

set_option synthInstance.maxHeartbeats 400000 in
-- Integral scalar change expands the fourfold graded tensor instance.
/-- Field-coefficient perfectness: bounded finite-dimensional cohomology of all four complexes.
Source: latest blueprint thm-pod-point-perfectness
(blueprint: thm-pod-point-perfectness).

Proof plan:
1. Base change preserves separated finite type. Choose a dense compactification, of the
same dimension. Finite direct-image bounds give [a,b+2d] for ordinary sections; exact
extension by zero and proper direct image give the same interval for compact support.
2. Direct-image stability puts both point objects in Dctf. Finite scalar local models
and split covers of the algebraically closed point give perfect scalar models; shifts,
cones and summands preserve them. Exact point sections recover these scalar models.
3. Finite-projective duals reverse the interval. Over the integral DVR the cohomology
is finitely generated; over fields it is finite dimensional. Descend algebraic-closure
objects to a finite extension using the condensed two-colimit theorem.
4. Scalar-six comparisons identify integral reductions with the finite-level images.
Finite-projective tensor-Hom gives the same comparison for duals. A single bounded
projective model and its dual give intervals independent of the positive level n.
5. For proper X₀ the base-changed structure map is proper. The canonical mate comparison
between compact and ordinary image is an isomorphism; point evaluation preserves it.
The cited DAG plan is cor-sf-direct-image-ctf-proetale, det-thm-sf-ctf-stability-direct-images,
det-prop-scalar-six-ctf, lem-weil-point-proetale-sections-exact,
lem-sfb-perfect-scalar-change-model, lem-weil-bounded-finite-tor-perfect,
sk-thm-sfb-qlbar-two-colimit and prop-weil-proper-compact-coincidence. -/
theorem condensed_point_perfectness_qbar (hl : l ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom)
    (K : sfCondensedDerived (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} l) (D.geometricFiber
        X₀).left K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    (∀ compact dual : Bool,
      DerivedCategory.IsPerfectRingComplex (condensedFourCohomology (Profinite.padicAlgClRingObj.{u}
          l) c K compact dual) ∧
      DerivedCategory.TStructure.t.bounded (condensedFourCohomology (Profinite.padicAlgClRingObj.{u}
          l) c K compact dual) ∧
      (∀ i : ℤ, Module.Finite (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l))
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l))) i).obj
            (condensedFourCohomology (Profinite.padicAlgClRingObj.{u} l) c K compact dual)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
