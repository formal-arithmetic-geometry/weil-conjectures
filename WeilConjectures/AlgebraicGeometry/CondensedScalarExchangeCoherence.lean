/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import all WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Condensed scalar exchange coherence

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/
lem-fix-operation-reduction.proof.md, paragraphs 2--3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofHasKInjectiveResolutions

/-- The canonical identity geometric unitor, with the existing scalar interface exposed.
Source: inverse-image identity, blueprint operation reduction, paragraph 3.
(blueprint: lem-fix-condensed-scalar-exchange-coherence). -/
def exchangeScalarIdentity
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) : L R (𝟙 X) ≅ 𝟭 _ := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarId R X

section IdentityUnit

attribute [local semireducible] L
attribute [local implicit_reducible] L CondensedRing.moduleObjectDerivedPullback

end IdentityUnit

/-- Horizontal and vertical pasting for the specified geometric exchange mates.
Together with the scalar comparison composition and cube equations, these are
pasting coherence of the scalar/exchange rectangle. Composite adjunctions and
pullback squares retain their canonical geometric compositors.
Source: latest blueprint operation reduction, paragraph 3; mate-pasting (1),(2).
(blueprint: lem-fix-condensed-scalar-exchange-coherence).

Proof: scalarAmbientExchange is by definition the mate of scalarPullbackSquare
under the geometric adjunctions. Horizontal pasting is then the generic mate law
mateEquiv_vcomp, and vertical pasting is mateEquiv_hcomp for the composite
adjunctions; both hold for any squares, so no scalar or geometric hypothesis is
used. No exchange or direct-image mate is assumed invertible. -/
theorem condensedScalarExchangePasting
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (∀ {X₂ X₁ X₀ Y₂ Y₁ Y₀ : Scheme.{u}}
      {u₁ : X₁ ⟶ X₀} {u₂ : X₂ ⟶ X₁}
      {v₁ : Y₁ ⟶ Y₀} {v₂ : Y₂ ⟶ Y₁}
      {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
      (s₁ : ChosenCartesianSquare u₁ f₁ f₀ v₁)
      (s₂ : ChosenCartesianSquare u₂ f₂ f₁ v₂),
      mateEquiv (adj R f₀) (adj R f₂)
          (TwoSquare.hComp
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)) =
        TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₁))
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₂))) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}}
      {u : X' ⟶ X} {v : Y' ⟶ Y} {w : Z' ⟶ Z}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
      (s₁ : ChosenCartesianSquare u f' f v)
      (s₂ : ChosenCartesianSquare v g' g w),
      mateEquiv ((adj R g).comp (adj R f)) ((adj R g').comp (adj R f'))
          (TwoSquare.vComp
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)
            (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)) =
        TwoSquare.hComp
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₁))
          (TwoSquare.mk _ _ _ _ (scalarAmbientExchange R s₂))) := by
  constructor
  · intro X₂ X₁ X₀ Y₂ Y₁ Y₀ u₁ u₂ v₁ v₂ f₀ f₁ f₂ s₁ s₂
    exact congrArg TwoSquare.natTrans
      (mateEquiv_vcomp (adj R f₀) (adj R f₁) (adj R f₂)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom))
  · intro X' X Y' Y Z' Z u v w f f' g g' s₁ s₂
    exact congrArg TwoSquare.natTrans
      (mateEquiv_hcomp (adj R g) (adj R g') (adj R f) (adj R f')
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₂).hom)
        (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R s₁).hom))

end AlgebraicGeometry.ProEtale.QuotientChange

open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofHasKInjectiveResolutions

private local instance compactRingComm (R : ScalarSixRing.{u}) : IsCommMonObj R.X := R.comm

private local instance compactMapMon {R S : ScalarSixRing.{u}} (a : R ⟶ S) :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.QuotientChange

set_option maxHeartbeats 800000 in
-- Compare the folded scalar and geometric functors before applying mate transport.
set_option maxHeartbeats 800000 in
-- Identify mates after rewriting their adjunctions and input squares.
set_option maxHeartbeats 1600000 in
-- Transport the inverse cube as a natural transformation before evaluating it.
set_option maxHeartbeats 800000 in
-- Check the concrete derived functor endpoints of the transported inverse mate.
set_option maxHeartbeats 800000 in
-- The unit equation compares the concrete composite derived functors.
section

attribute [local implicit_reducible] Compactification.baseChange
  Compactification.ofIsPullback CommMon.toMon scalarSixPull
  CondensedRing.moduleObjectDerivedPullback

attribute [local irreducible] Sheaf.monoidalCategory
  Mod.monoidalCategoryStruct Mod.monoidalClosed
attribute [local implicit_reducible] Mod.monoidalCategory Monoidal.induced
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory

set_option maxHeartbeats 1600000 in
-- The generic cube is instantiated at eight large derived module categories.
end

set_option maxHeartbeats 1600000 in
-- Transport the exchange factors using functor equalities before taking components.
attribute [local implicit_reducible] CommMon.toMon Compactification.baseChange
  Compactification.ofIsPullback CondensedRing.moduleObjectDerivedPushforward

set_option maxHeartbeats 1600000 in
-- Use the same folded scalar comparison on both sides of the compact support map.
set_option maxHeartbeats 1600000 in
-- Paste the proper and open equations before taking any components.
set_option maxHeartbeats 1600000 in
-- Evaluate the pasted natural transformation on the constructible input.
end AlgebraicGeometry.ProEtale.QuotientChange
