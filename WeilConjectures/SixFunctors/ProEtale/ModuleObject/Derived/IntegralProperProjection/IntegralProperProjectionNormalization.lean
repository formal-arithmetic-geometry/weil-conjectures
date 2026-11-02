/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProjectionAdjunctionNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
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
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
public import Mathlib.AlgebraicGeometry.Noetherian
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
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-! # Proper-coordinate projection and its condensed coefficient square

Source: latest blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, scalar compatibility and proper coincidence.
(blueprint: lem-sf-integral-proper-projection-system-normalization).

All operations act on ordinary unbounded internal-module derived categories. Exact
pullback is the recorded termwise presentation of total derived pullback; the projection
is transported by the published comparison between those presentations. Scalar change
is ordinary derived extension, including for nonflat quotient maps. The helpers below
spell out the maps named in the node, using the existing canonical factors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralProperProjection

private theorem joint_projection
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    {K K' : C} {L L' : D} (k : K ⟶ K') (l : L ⟶ L') :
    (G.map k ⊗ₘ l) ≫ ((adj.rightAdjointProjectionMap φ).app K').app L' =
      ((adj.rightAdjointProjectionMap φ).app K).app L ≫ G.map (k ⊗ₘ F.map l) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    adj.rightAdjointProjectionMap_naturality_right,
    ← Category.assoc, adj.rightAdjointProjectionMap_naturality_left,
    Category.assoc, ← G.map_comp, ← MonoidalCategory.tensorHom_def]

private theorem square_comp {C : Type*} [Category C]
    {A A' B B' D D' : C} {x : A ⟶ A'} {y : B ⟶ B'} {z : D ⟶ D'}
    {p : A ⟶ B} {p' : A' ⟶ B'} {q : B ⟶ D} {q' : B' ⟶ D'}
    (hp : x ≫ p' = p ≫ y) (hq : y ≫ q' = q ≫ z) :
    x ≫ (p' ≫ q') = (p ≫ q) ≫ z := by
  rw [← Category.assoc, hp, Category.assoc, hq, Category.assoc]

private theorem square_map {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A A' B B' : C}
    {x : A ⟶ A'} {y : B ⟶ B'} {p : A ⟶ B} {p' : A' ⟶ B'}
    (h : x ≫ p' = p ≫ y) : F.map x ≫ F.map p' = F.map p ≫ F.map y := by
  rw [← F.map_comp, h, F.map_comp]

private theorem square_tensor {C : Type*} [Category C] [MonoidalCategory C]
    {A A' B B' X X' Y Y' : C}
    {x : A ⟶ A'} {y : B ⟶ B'} {p : A ⟶ B} {p' : A' ⟶ B'}
    {v : X ⟶ X'} {w : Y ⟶ Y'} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    (hp : x ≫ p' = p ≫ y) (hq : v ≫ q' = q ≫ w) :
    (x ⊗ₘ v) ≫ (p' ⊗ₘ q') = (p ⊗ₘ q) ≫ (y ⊗ₘ w) := by
  rw [tensorHom_comp_tensorHom, hp, hq, ← tensorHom_comp_tensorHom]

private theorem square_whisker {C : Type*} [Category C] [MonoidalCategory C]
    {A A' B B' X X' : C}
    {x : A ⟶ A'} {y : B ⟶ B'} {p : A ⟶ B} {p' : A' ⟶ B'}
    (hp : x ≫ p' = p ≫ y) (v : X ⟶ X') :
    (x ⊗ₘ v) ≫ (p' ▷ X') = (p ▷ X) ≫ (y ⊗ₘ v) := by
  simpa only [tensorHom_id] using square_tensor hp
    (show v ≫ 𝟙 X' = 𝟙 X ≫ v by simp)

private theorem square_whisker_left {C : Type*} [Category C] [MonoidalCategory C]
    {A A' B B' X X' : C}
    {x : A ⟶ A'} {y : B ⟶ B'} {p : A ⟶ B} {p' : A' ⟶ B'}
    (hp : x ≫ p' = p ≫ y) (v : X ⟶ X') :
    (v ⊗ₘ x) ≫ (X' ◁ p') = (X ◁ p) ≫ (v ⊗ₘ y) := by
  simpa only [id_tensorHom] using square_tensor
    (show v ≫ 𝟙 X' = 𝟙 X ≫ v by simp) hp

private theorem inverse_square {C : Type*} [Category C]
    {A A' B B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (x : A ⟶ A') (y : B ⟶ B') (h : x ≫ e'.hom = e.hom ≫ y) :
    y ≫ e'.inv = e.inv ≫ x := by
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [← h, Category.assoc, e'.hom_inv_id, Category.comp_id]

private theorem tensorator_square {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (T : C ⥤ D) [T.Monoidal]
    {A A' B B' : C} (k : A ⟶ A') (l : B ⟶ B') :
    T.map (k ⊗ₘ l) ≫ (Functor.Monoidal.μIso T A' B').inv =
      (Functor.Monoidal.μIso T A B).inv ≫ (T.map k ⊗ₘ T.map l) := by
  exact inverse_square (Functor.Monoidal.μIso T A B)
    (Functor.Monoidal.μIso T A' B') _ _ (Functor.LaxMonoidal.μ_natural T k l)

private theorem joint_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (α : F ⟶ G)
    {K K' : C} {L L' : D} (k : K ⟶ K') (l : L ⟶ L') :
    (F.map k).app L ≫ (F.obj K').map l ≫ (α.app K').app L' =
      (α.app K).app L ≫ (G.map k).app L ≫ (G.obj K').map l := by
  rw [(α.app K').naturality, ← Category.assoc]
  have h := NatTrans.congr_app (α.naturality k) L
  simp only [NatTrans.comp_app] at h
  rw [h, Category.assoc]

private theorem joint_open_projection
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {J : C ⥤ D} {F : D ⥤ C} (adj : J ⊣ F)
    (δ : (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj F).obj (curriedTensor D))
    {K K' : C} {L L' : D} (k : K ⟶ K') (l : L ⟶ L') :
    J.map (k ⊗ₘ F.map l) ≫
        ((adj.projectionMap F (curriedTensor C) (curriedTensor D) δ).app K').app L' =
      ((adj.projectionMap F (curriedTensor C) (curriedTensor D) δ).app K).app L ≫
        (J.map k ⊗ₘ l) := by
  have h := joint_naturality
    (adj.projectionMap F (curriedTensor C) (curriedTensor D) δ) k l
  change J.map (k ▷ F.obj L) ≫ J.map (K' ◁ F.map l) ≫ _ =
    _ ≫ (J.map k ▷ L) ≫ (J.obj K' ◁ l) at h
  simpa only [← J.map_comp_assoc, MonoidalCategory.tensorHom_def, Category.assoc,
    Functor.id_obj] using h

private theorem inverse_family_square {C : Type*} [Category C]
    {A A' B B' : C} (p : A ⟶ B) (p' : A' ⟶ B')
    (q : B ⟶ A) (q' : B' ⟶ A') (x : A ⟶ A') (y : B ⟶ B')
    (h : x ≫ p' = p ≫ y) (hq : q ≫ p = 𝟙 B) (hq' : p' ≫ q' = 𝟙 A') :
    y ≫ q' = q ≫ x := by
  calc
    y ≫ q' = (q ≫ p) ≫ y ≫ q' := by rw [hq, Category.id_comp]
    _ = q ≫ (p ≫ y) ≫ q' := by simp only [Category.assoc]
    _ = q ≫ (x ≫ p') ≫ q' := by rw [← h]
    _ = q ≫ x := by simp only [Category.assoc, hq', Category.comp_id]

private theorem identity_unit_of_counit {C : Type*} [Category C] {J F : C ⥤ C}
    (a : J ⊣ F) (e : J ≅ 𝟭 C) (p : F ≅ 𝟭 C)
    (hc : ∀ N, e.inv.app (F.obj N) ≫ a.counit.app N = p.hom.app N) (K : C) :
    a.unit.app K ≫ p.hom.app (J.obj K) = e.inv.app K := by
  rw [← hc, ← Category.assoc]
  have hn := e.inv.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [hn, Category.assoc, a.left_triangle_components, Category.comp_id]

private theorem identity_projection
    {C : Type*} [Category C] [MonoidalCategory C]
    {J F : C ⥤ C} (a : J ⊣ F) (e : J ≅ 𝟭 C) (p : F ≅ 𝟭 C)
    (δ : (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj F).obj (curriedTensor C))
    (hu : ∀ K, a.unit.app K ≫ p.hom.app (J.obj K) = e.inv.app K)
    (hd : ∀ A B, (δ.app A).app B ≫ p.hom.app (A ⊗ B) =
      p.hom.app A ⊗ₘ p.hom.app B) (K V : C) :
    ((a.projectionMap F (curriedTensor C) (curriedTensor C) δ).app K).app V ≫
        (e.hom.app K ▷ V) =
      J.map (K ◁ p.hom.app V) ≫ e.hom.app (K ⊗ V) := by
  have hunit (A : C) : a.unit.app A ≫ F.map (e.hom.app A) = p.inv.app A := by
    apply (cancel_mono (p.hom.app A)).1
    have hn := p.hom.naturality (e.hom.app A)
    simp only [Functor.id_obj, Functor.id_map] at hn
    rw [Category.assoc, hn]
    simp only [← Category.assoc, hu, Iso.inv_hom_id_app]
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, F.map_comp]
  rw [← Category.assoc, a.unit_app_comp_map_projectionMap_app_app]
  change ((a.unit.app K ▷ F.obj V) ≫ (δ.app (J.obj K)).app V) ≫
      F.map (e.hom.app K ▷ V) =
    a.unit.app (K ⊗ F.obj V) ≫
      F.map (J.map (K ◁ p.hom.app V)) ≫ F.map (e.hom.app (K ⊗ V))
  have hn := NatTrans.congr_app (δ.naturality (e.hom.app K)) V
  change (F.map (e.hom.app K) ▷ F.obj V) ≫ (δ.app K).app V =
    (δ.app (J.obj K)).app V ≫ F.map (e.hom.app K ▷ V) at hn
  rw [Category.assoc, ← hn, ← comp_whiskerRight_assoc, hunit]
  have he := e.hom.naturality (K ◁ p.hom.app V)
  simp only [Functor.id_obj, Functor.id_map] at he
  rw [← F.map_comp, he]
  simp only [F.map_comp, ← Category.assoc, hunit]
  apply (cancel_mono (p.hom.app (K ⊗ V))).1
  have hp := p.hom.naturality (K ◁ p.hom.app V)
  simp only [Functor.id_obj, Functor.id_map] at hp
  rw [Category.assoc, hd, Category.assoc, hp]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id_app, Functor.id_obj, Category.id_comp, id_tensorHom]

private theorem inverse_identity_projection
    {C : Type*} [Category C] [MonoidalCategory C]
    {J F : C ⥤ C} (e : J ≅ 𝟭 C) (p : F ≅ 𝟭 C) (K V : C)
    (π : J.obj (K ⊗ F.obj V) ⟶ J.obj K ⊗ V)
    (q : J.obj K ⊗ V ⟶ J.obj (K ⊗ F.obj V))
    (hπ : π ≫ (e.hom.app K ▷ V) =
      J.map (K ◁ p.hom.app V) ≫ e.hom.app (K ⊗ V))
    (hq : q ≫ π = 𝟙 _) :
    (q ≫ J.map (K ◁ p.hom.app V)) ≫ e.hom.app (K ⊗ V) = e.hom.app K ▷ V := by
  rw [Category.assoc, ← hπ, ← Category.assoc, hq, Category.id_comp]

private theorem tensor_transport_identity
    {C : Type*} [Category C] [MonoidalCategory C] {T F : C ⥤ C}
    (e : T ≅ F) (p : F ≅ 𝟭 C) (t : T ≅ 𝟭 C)
    (he : e ≪≫ p = t) (A B : C)
    (φ : T.obj (A ⊗ B) ⟶ T.obj A ⊗ T.obj B)
    (hφ : φ ≫ (t.hom.app A ⊗ₘ t.hom.app B) = t.hom.app (A ⊗ B)) :
    (e.inv.app (A ⊗ B) ≫ φ ≫ (e.hom.app A ⊗ₘ e.hom.app B)) ≫
        (p.hom.app A ⊗ₘ p.hom.app B) = p.hom.app (A ⊗ B) := by
  have hh (M : C) : e.hom.app M ≫ p.hom.app M = t.hom.app M := by
    exact NatTrans.congr_app (congrArg Iso.hom he) M
  rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom, hh, hh, hφ,
    ← hh, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem inverse_tensor_identity
    {C : Type*} [Category C] [MonoidalCategory C] {F : C ⥤ C}
    (p : F ≅ 𝟭 C) (A B : C) (φ : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (h : φ.hom ≫ (p.hom.app A ⊗ₘ p.hom.app B) = p.hom.app (A ⊗ B)) :
    φ.inv ≫ p.hom.app (A ⊗ B) = p.hom.app A ⊗ₘ p.hom.app B := by
  rw [← h, ← Category.assoc, φ.inv_hom_id, Category.id_comp]

private theorem normalize_coordinate
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {J : C ⥤ C} (R : C ⥤ D) (e : J ≅ 𝟭 C) (K V : C) (L : D)
    (g : J.obj K ⊗ V ⟶ J.obj (K ⊗ V))
    (π : R.obj (J.obj K) ⊗ L ⟶ R.obj (J.obj K ⊗ V))
    (π' : R.obj K ⊗ L ⟶ R.obj (K ⊗ V))
    (hg : g ≫ e.hom.app (K ⊗ V) = e.hom.app K ▷ V)
    (hπ : (R.map (e.hom.app K) ▷ L) ≫ π' = π ≫ R.map (e.hom.app K ▷ V)) :
    (R.mapIso (e.app K)).inv ▷ L ≫ (π ≫ R.map g) ≫
      (R.mapIso (e.app (K ⊗ V))).hom = π' := by
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [← R.map_comp, hg, ← hπ, ← Category.assoc, ← comp_whiskerRight,
    ← R.map_comp, Iso.inv_hom_id_app, R.map_id, id_whiskerRight, Category.id_comp]

/-- The proper-coordinate isomorphism q_M = R(e_M), for the specified identity-open e.
Source: latest blueprint fix-prop-projection-formula.proof.md, proper coincidence
(blueprint: lem-sf-integral-proper-projection-system-normalization). -/
def coordinateIso (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (RootCoordinateFace.lower Λ.X f).obj
        ((openImmersionLowerShriek Λ.X (𝟙 X)).mapDerivedCategory.obj M) ≅
      (RootCoordinateFace.lower Λ.X f).obj M :=
  (RootCoordinateFace.lower Λ.X f).mapIso
    ((derivedOpenImmersionLowerShriekId Λ.X X).app M)

private theorem coordinateIso_naturality
    {Λ : ScalarSixRing.{u}} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (k : K ⟶ K') :
    (RootCoordinateFace.lower Λ.X f).map
          ((openImmersionLowerShriek Λ.X (𝟙 X)).mapDerivedCategory.map k) ≫
        (coordinateIso Λ f K').hom =
      (coordinateIso Λ f K).hom ≫
        (RootCoordinateFace.lower Λ.X f).map k := by
  simp only [coordinateIso, Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simpa only [Functor.id_map] using congrArg (RootCoordinateFace.lower Λ.X f).map
    ((derivedOpenImmersionLowerShriekId Λ.X X).hom.naturality k)

private theorem coordinateInv_natural
    {Λ : ScalarSixRing.{u}} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)} (k : K ⟶ K') :
    (RootCoordinateFace.lower Λ.X f).map k ≫ (coordinateIso Λ f K').inv =
      (coordinateIso Λ f K).inv ≫ (RootCoordinateFace.lower Λ.X f).map
        ((openImmersionLowerShriek Λ.X (𝟙 X)).mapDerivedCategory.map k) := by
  exact inverse_square _ _ _ _ (coordinateIso_naturality f K K' k)

private theorem exact_identity_counit (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (V : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (derivedOpenImmersionLowerShriekId Λ.X X).inv.app ((scalarSixPull Λ (𝟙 X)).obj V) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (𝟙 X)).counit.app V =
    (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app V := by
  exact Adjunction.mapDerivedCategoryAdjunction_counit_app_of_iso
    (openImmersionLowerShriekUpperStarAdjunction Λ.X (𝟙 X))
    (openImmersionLowerShriekId Λ.X X) (upperStarId Λ.X X)
    (Adjunction.leftAdjointUniq_ofNatIsoRight_inv_app_comp_counit _ _) V

private theorem exact_identity_comparison (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    leftDerivedUpperStarIsoMapDerivedCategory Λ.X (𝟙 X) ≪≫
      (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
        Functor.mapDerivedCategoryIdIso _) = leftDerivedUpperStarId Λ.X X := by
  simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorIdIso,
    Functor.leftDerivedFunctorNatIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem exact_identity_tensor (Λ : ScalarSixRing.{u}) (X : Scheme.{u})
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    ((condensedProjectionPullTensor Λ (𝟙 X)).inv.app A).app B ≫
      (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (A ⊗ B) =
    (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app A ⊗ₘ
      (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app B := by
  let p := Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  have ht := tensor_transport_identity (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (𝟙 X))
    p (leftDerivedUpperStarId Λ.X X) (exact_identity_comparison Λ X) A B _
    (leftDerivedUpperStarTensor_id Λ.X X A B)
  have hφ := congrArg (fun z ↦ z ≫ (p.hom.app A ⊗ₘ p.hom.app B))
    (pullTensor_hom Λ (𝟙 X) A B)
  exact inverse_tensor_identity p A B
    (((condensedProjectionPullTensor Λ (𝟙 X)).app A).app B) (hφ.trans ht)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralProperProjection
