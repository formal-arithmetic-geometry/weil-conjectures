/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointTrivializationComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import Mathlib.Lean.Meta.CongrTheorems
meta import Mathlib.Lean.Meta.CongrTheorems

/-! # Composition of semilinear condensed cohomology transports

Source: latest blueprint, sec-trace-formula/sk-thm-tf-uniform-formula,
second and final paragraphs of sk-thm-tf-uniform-formula.proof.md.
(blueprint: lem-trf-condensed-cohomology-transport-composition)

The compositor is displayed on the target, so the order of the two transports
is unambiguous even for distinct schemes and nontrivial base automorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

section CompositionProof

/- This is the explicit congruence construction used in CondensedPointModuleComparison.
It proves conversion of implicit proof arguments without expanding sheafification choices.
Functor composition and identity projections are reduced before structural comparison.
Every generated equality is checked by the kernel. -/
local syntax (name := compositionStructuralExact) "composition_structural_exact " term : tactic

meta section
open Lean Meta Elab Tactic
termination_by fuel
end

open Lean Meta Elab Tactic in
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction leftDerivedUpperStarComp
  pullbackSquareComparison
attribute [local implicit_reducible] moduleObjectDerivedPullback

set_option maxHeartbeats 1000000 in
-- Keep native derived functors fixed throughout mate and insertion pasting.
set_option maxHeartbeats 1000000 in
-- Convert the completed native pasting proof to the published functor aliases.
set_option maxHeartbeats 1000000 in
-- Compare canonical compactification models through the native functor API.
end CompositionProof

/-- The actual map on the ordinary rings Λ(*), obtained by terminal evaluation.
Source: blueprint, the coefficient comparisons at the condensed point.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
def transportScalarMap {A B : ScalarSixRing.{u}} (a : A ⟶ B) :
    condensedScalarRing A.X →+* condensedScalarRing B.X :=
  ((InternalAbelianSheafModule.sectionScalarMap (coherentTopology Profinite.{u})
    (R := A.X) (S := B.X) a.hom.hom).hom.app
      (Opposite.op (⊤_ Profinite.{u}))).hom

/-- Ordinary derived extension on Λ(*) with its canonical extension/restriction adjunction.
Source: blueprint, uncompleted scalar extension on cohomology.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
def transportScalarAdjunction {A B : ScalarSixRing.{u}} (a : A ⟶ B) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (transportScalarMap a)).leftDerivedFunctor ⊣
      (ModuleCat.restrictScalars.{u + 1} (transportScalarMap a)).mapDerivedCategory :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1}
    (transportScalarMap a)).derivedAdjunction).ofNatIsoRight
    (ModuleCat.restrictScalars.{u + 1}
      (transportScalarMap a)).rightDerivedFunctorIsoMapDerivedCategory

/-- The restriction/sections comparison, fixed on every section by the identity function.
This normalizes its derived comparison on every representative complex, not only H⁰.
Source: blueprint, the restriction reparametrization in the coefficient squares.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
structure TransportScalarSections {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] where
  restriction :
    Mod.comap (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom (Spec (.of k))) ⋙
        sections A.X (Spec (.of k)) ≅
      sections B.X (Spec (.of k)) ⋙ ModuleCat.restrictScalars.{u + 1} (transportScalarMap a)
  normalized : ∀ (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj B.X (Spec (.of k))))
    (x : N.X.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec (.of k)))))),
    HEq ((restriction.hom.app N).hom x) x

/-- Localize the sectionwise identity and use the canonical exact-to-derived identifications.
Source: blueprint, the same restriction reparametrization on ordinary derived categories.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
def TransportScalarSections.derivedRestriction {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {k : Type u} [Field k] [IsAlgClosed k] (P : TransportScalarSections a k) :
    (Mod.comap (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom
      (Spec (.of k)))).mapDerivedCategory ⋙ Γ A.X (Spec (.of k)) ≅
      Γ B.X (Spec (.of k)) ⋙
        (ModuleCat.restrictScalars.{u + 1} (transportScalarMap a)).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (sections A.X (Spec (.of k))).rightDerivedFunctorIsoMapDerivedCategory
    ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
    ≪≫ Functor.mapDerivedCategoryNatIso P.restriction
    ≪≫ Functor.mapDerivedCategoryCompIso _ _
    ≪≫ Functor.isoWhiskerRight
      (sections B.X (Spec (.of k))).rightDerivedFunctorIsoMapDerivedCategory.symm _

/-- The scalar cohomology comparison is the adjunction mate of normalized restriction.
Thus no arbitrary comparison natural transformation is part of the theorem's data.
Source: blueprint, scalar extension of cohomology transport.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
def TransportScalarSections.comparison {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {k : Type u} [Field k] [IsAlgClosed k] (P : TransportScalarSections a k) :
    Γ A.X (Spec (.of k)) ⋙
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (transportScalarMap a)).leftDerivedFunctor ⟶
      scalarSixChange a (Spec (.of k)) ⋙ Γ B.X (Spec (.of k)) :=
  ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom (Spec (.of k))))
      (transportScalarAdjunction a)).symm
        (TwoSquare.mk _ _ _ _ (P.derivedRestriction a).hom)).natTrans

/-- The canonical scalar pullback square, with total derived pullbacks at both endpoints.
Source: blueprint, pullback coefficient comparison and its compositor normalization.
(blueprint: lem-trf-condensed-cohomology-transport-composition) -/
def transportScalarPull {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A.X f ⋙ scalarSixChange a X ⟶ scalarSixChange a Y ⋙ L B.X f :=
  Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A.X f).hom
      (scalarSixChange a X) ≫ scalarSixPullHom a f ≫
    Functor.whiskerLeft (scalarSixChange a Y)
      (leftDerivedUpperStarIsoMapDerivedCategory B.X f).inv

section IterationProof

universe v

set_option Elab.async false

set_option maxHeartbeats 1000000 in
-- Compare the recursion callbacks before applying the generic successor equation.
set_option maxHeartbeats 1000000 in
-- Compare the recursion callbacks before applying the generic successor equation.
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction leftDerivedUpperStarComp
attribute [local implicit_reducible]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  moduleObjectDerivedPullback

-- Use the native tensor structures without expanding sheafification choices.
-- This is the local reduction convention of CondensedScalarExchangeCoherence.
attribute [local irreducible] Sheaf.monoidalCategory
  Mod.monoidalCategoryStruct Mod.monoidalClosed
attribute [local implicit_reducible] Mod.monoidalCategory Monoidal.induced
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

set_option maxHeartbeats 1000000 in
-- Comparing native total-derived functor types needs a larger conversion budget.
set_option maxHeartbeats 1000000 in
-- Normalize the native compositor once, before using the equation in the induction.
set_option maxHeartbeats 1000000 in
-- Comparing native total-derived functor types needs a larger conversion budget.
end IterationProof

end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
