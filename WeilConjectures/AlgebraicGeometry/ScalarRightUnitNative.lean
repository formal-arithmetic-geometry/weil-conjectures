/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
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
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.Tensor.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.CategoryTheory.ScalarRightUnitAtRepresentative
import WeilConjectures.CategoryTheory.Scalar.ScalarRightUnitTransport

/-! # Native K-flat normalization and right-unit coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
open MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale
attribute [local instance] currentScalarSmall scalarModulesMonoidal
  scalarModulesPreadditive scalarMonoidal
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

/-- The total tensor of K-flat representatives is K-flat.
Source: Stacks 06YS (blueprint: lem-pur-scalar-right-unit-native).
Proof: tensor an acyclic complex first with P and then with Q. Both results are
acyclic by K-flatness; the total-complex associator identifies the second result
with tensoring by P tensor Q. -/
theorem scalarComplex_tensor_kflat {A : Type u} [CommRing A] (T : Scheme.{u})
    (P Q : ScalarComplex T A)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := proEtaleConstantRing T A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := proEtaleConstantRing T A) Q) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := proEtaleConstantRing T A)
      ((WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
        (ProEt.topology T) (proEtaleConstantRing T A)).obj (P, Q)) := by
  exact WeilConjectures.coefficientTotalTensor_isKFlat.{0, u + 1, u}
    (ProEt.topology T) (proEtaleConstantRing T A) P Q hP hQ

/-- The coefficient ring in degree zero is K-flat.
Source: Stacks 06YS (blueprint: lem-pur-scalar-right-unit-native).
Proof: tensoring an acyclic complex with the unit is isomorphic to that complex
by the right unitor, so remains acyclic. -/
theorem scalarComplex_unit_kflat {A : Type u} [CommRing A] (T : Scheme.{u}) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := proEtaleConstantRing T A) (𝟙_ (ScalarComplex T A)) := by
  intro Z hZ n
  exact (hZ n).of_iso (ρ_ Z).symm

/-- The degree-zero coefficient unit has flat terms, including its zero terms.
Source: Stacks 06YS (blueprint: lem-pur-scalar-right-unit-native).
Proof: its term in degree zero is the tensor unit and tensoring by it is the
identity up to the unitor. Each other term is zero, hence flat.
-/
theorem scalarComplex_unit_flat {A : Type u} [CommRing A] (T : Scheme.{u}) :
    ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (proEtaleConstantRing T A))
        ((𝟙_ (ScalarComplex T A)).X i)) := by
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
  intro i
  by_cases hi : i = 0
  · subst i
    exact (ObjectProperty.prop_unit ObjectProperty.flat).2
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (𝟙_ (proEtaleRingModules T (proEtaleConstantRing T A))) i hi
    exact (ObjectProperty.flat_of_isZero hz).2

/-- The explicitly constructed unit satisfies its localization normalization.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-scalar-right-unit-native).
Proof: expand the unit map and cancel the inverse and forward native unit
comparison at B. -/
theorem proEtaleScalarUnit_normalized {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : ProEtaleScalarUnitNormalized φ T := by
  simp only [ProEtaleScalarUnitNormalized, proEtaleScalarUnit, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The concrete scalar tensor comparison is invertible.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-scalar-right-unit-native).
Proof: both chosen representatives are K-flat and their total tensor is K-flat.
The actual scalar counit on that tensor is therefore invertible. Every other
factor in the displayed definition is a functor image, tensor, or composite of
isomorphisms. -/
theorem proEtaleScalarTensor_isIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K L : proEtaleDerivedCategory T A) :
    IsIso (proEtaleScalarTensor φ T K L) := by
  have := currentScalarCounit_isIso φ T
    ((scalarFlatRepresentative T K).complex ⊗ (scalarFlatRepresentative T L).complex)
    (scalarComplex_tensor_kflat T _ _
      (scalarFlatRepresentative T K).kflat (scalarFlatRepresentative T L).kflat)
  dsimp only [proEtaleScalarTensor]
  infer_instance

/-- The concrete scalar unit comparison is invertible.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-scalar-right-unit-native).
Proof: the source coefficient ring in degree zero is K-flat, so its actual
scalar counit is invertible. The remaining factors are the native unit
comparisons and localization of the balanced unit isomorphism. -/
theorem proEtaleScalarUnit_isIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : IsIso (proEtaleScalarUnit φ T) := by
  have := currentScalarCounit_isIso φ T (𝟙_ (ScalarComplex T A))
    (scalarComplex_unit_kflat T)
  dsimp only [proEtaleScalarUnit]
  infer_instance

private theorem tensorComparison_component
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (a : tensor C ⋙ S ≅ S.prod S ⋙ tensor D)
    {P Q K L V : C} {EP EQ W : D}
    (p : P ≅ K) (q : Q ≅ L) (iA : V ≅ P ⊗ Q)
    (iB : W ≅ EP ⊗ EQ) (cP : S.obj P ≅ EP) (cQ : S.obj Q ≅ EQ)
    (z : S.obj V ⟶ W)
    (h : S.map iA.hom ≫ a.hom.app (P, Q) ≫ (cP.hom ⊗ₘ cQ.hom) = z ≫ iB.hom) :
    a.hom.app (K, L) =
      S.map ((tensorIso p q).inv ≫ iA.inv) ≫ z ≫ iB.hom ≫
        (cP.inv ⊗ₘ cQ.inv) ≫ (S.map p.hom ⊗ₘ S.map q.hom) := by
  have hform : a.hom.app (P, Q) =
      S.map iA.inv ≫ z ≫ iB.hom ≫ (cP.inv ⊗ₘ cQ.inv) := by
    apply (cancel_epi (S.map iA.hom)).1
    apply (cancel_mono (cP.hom ⊗ₘ cQ.hom)).1
    have hc : (cP.inv ⊗ₘ cQ.inv) ≫ (cP.hom ⊗ₘ cQ.hom) = 𝟙 _ := by
      rw [tensorHom_comp_tensorHom, cP.inv_hom_id, cQ.inv_hom_id,
        id_tensorHom_id]
    simp only [Category.assoc]
    rw [← S.map_comp_assoc, iA.hom_inv_id, S.map_id, Category.id_comp]
    rw [hc, Category.comp_id]
    exact h
  have hn := a.hom.naturality (Prod.mkHom p.hom q.hom)
  change S.map (tensorIso p q).hom ≫ a.hom.app (K, L) =
    a.hom.app (P, Q) ≫ (S.map p.hom ⊗ₘ S.map q.hom) at hn
  apply (cancel_epi (S.map (tensorIso p q).hom)).1
  rw [hn, hform]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc, Category.assoc]

set_option maxHeartbeats 2000000 in
-- Normalize several large functor and native tensor comparison expressions.
/-- The concrete tensor map is the component of a natural comparison and has
its prescribed normalization on every flat-term K-flat representative.
Source: Stacks 06YS, 06YY, 07A4
(blueprint: lem-pur-scalar-right-unit-native).
Proof: restrict localization to flat-term K-flat representatives. Ore roofs and
resolutions make two-variable restriction fully faithful. Descend the balanced
cochain comparison using the counit and the native tensor models. Naturality at
the two chosen resolution isomorphisms identifies its component with the formula
in proEtaleScalarTensor. Its normalization square is therefore the displayed one.
-/
theorem proEtaleScalarTensor_natural_normalized
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (∃ a : tensor (proEtaleDerivedCategory T A) ⋙ scalarExtensionFunctor φ T ≅
        (scalarExtensionFunctor φ T).prod (scalarExtensionFunctor φ T) ⋙
          tensor (proEtaleDerivedCategory T B),
      ∀ K L, a.hom.app (K, L) = proEtaleScalarTensor φ T K L) ∧
      ProEtaleScalarTensorNormalized φ T := by
  let A₀ := proEtaleRingModules T (proEtaleConstantRing T A)
  let B₀ := proEtaleRingModules T (proEtaleConstantRing T B)
  let E := CochainPullback.extend.{u + 1, u + 1, u}
    (proEtaleConstantRingMap (T := T) φ)
  let S := scalarExtensionFunctor φ T
  let PA : ObjectProperty (ScalarComplex T A) := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T A) P ∧
      ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (P.X i))
  let PB : ObjectProperty (ScalarComplex T B) :=
    CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T B)
  have hE : ∀ P, PA P → PB (E.obj P) := by
    intro P hP
    exact (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (proEtaleConstantRingMap (T := T) φ) P
      (CochainPullback.extensionFunctor.{u + 1, u + 1, u}
        (proEtaleConstantRingMap (T := T) φ)) (fun _ ↦ rfl)
      (fun g ↦ CochainPullback.extensionFunctor_mapPresentation
        (proEtaleConstantRingMap (T := T) φ) g) hP.1 hP.2).1
  let H : ObjectProperty (HomotopyCategory A₀ (.up ℤ)) := fun X ↦ PA X.as
  have hres : ∀ X : HomotopyCategory A₀ (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A₀ (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := proEtaleConstantRing T A) X.as
    refine ⟨⟨(HomotopyCategory.quotient A₀ (.up ℤ)).obj P, hp, hf⟩,
      (HomotopyCategory.quotient A₀ (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := ScalarComplex T A) (H := HomotopyCategory A₀ (.up ℤ))
    (D := proEtaleDerivedCategory T A) (proEtaleDerivedCategory T B)
    (HomotopyCategory.quotient A₀ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A₀ (.up ℤ)) DerivedCategory.Qh PA H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (proEtaleDerivedCategory T B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PA.ι (DerivedCategory.quotientCompQhIso A₀))
      (Functor.isoWhiskerLeft PA.ι (DerivedCategory.quotientCompQhIso A₀))))
  let tA := WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
    (ProEt.topology T) (proEtaleConstantRing T A)
  let tB := WeilConjectures.coefficientTotalTensor.{0, u + 1, u}
    (ProEt.topology T) (proEtaleConstantRing T B)
  let rA : (PA.ι.prod PA.ι) ⋙ tA ⋙ DerivedCategory.Q ≅
      ((PA.ι ⋙ DerivedCategory.Q).prod (PA.ι ⋙ DerivedCategory.Q)) ⋙
        tensor (proEtaleDerivedCategory T A) :=
    NatIso.ofComponents (fun X ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T A) X.1.obj X.2.obj (Or.inl X.1.property.1))
      (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
        (ProEt.topology T) (proEtaleConstantRing T A) _ _ _ _ _ _ f.1.hom f.2.hom)
  let rB := RingedDerivedNative.comparison.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B)
  let b : tA ⋙ E ≅ E.prod E ⋙ tB := NatIso.ofComponents
    (fun X ↦ scalarComplexTensor φ T X.1 X.2) (by
      intro X Y f
      change E.map ((f.1 ▷ X.2) ≫ (Y.1 ◁ f.2)) ≫
          (scalarComplexTensor φ T Y.1 Y.2).hom =
        (scalarComplexTensor φ T X.1 X.2).hom ≫
          ((E.map f.1 ▷ E.obj X.2) ≫ (E.obj Y.1 ◁ E.map f.2))
      rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def]
      exact
        (CochainPullback.cochainComparison_monoidal.{u + 1, u + 1, u, u + 1, u}
        (CochainPullback.extensionPullback.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ))
        (CochainPullback.extensionComparison.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ))).1
          X.1 X.2 Y.1 Y.2 f.1 f.2)
  obtain ⟨a, ha, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q E S (currentScalarCounitNat φ T)
    PA PB hE ff' tA tB (tensor (proEtaleDerivedCategory T A))
      (tensor (proEtaleDerivedCategory T B)) rA rB b
    (fun P hP ↦ currentScalarCounit_isIso φ T P hP.1)
    (fun P Q hP hQ ↦ currentScalarCounit_isIso φ T _
      (scalarComplex_tensor_kflat T P Q hP.1 hQ.1))
  have heq (K L : proEtaleDerivedCategory T A) :
      a.hom.app (K, L) = proEtaleScalarTensor φ T K L := by
    let P := scalarFlatRepresentative T K
    let Q := scalarFlatRepresentative T L
    let iA := RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T A)
        P.complex Q.complex (Or.inl P.kflat)
    let iB := RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T B)
        (E.obj P.complex) (E.obj Q.complex) (Or.inl (hE P.complex ⟨P.kflat, P.flat⟩))
    let cP := currentScalarKFlatIso φ T P.complex P.kflat
    let cQ := currentScalarKFlatIso φ T Q.complex Q.kflat
    let e := tensorIso P.iso Q.iso
    have h := ha P.complex Q.complex ⟨P.kflat, P.flat⟩ ⟨Q.kflat, Q.flat⟩
    change S.map iA.hom ≫ a.hom.app
        (DerivedCategory.Q.obj P.complex, DerivedCategory.Q.obj Q.complex) ≫
          (cP.hom ⊗ₘ cQ.hom) =
      currentScalarCounit φ T (P.complex ⊗ Q.complex) ≫
        DerivedCategory.Q.map (scalarComplexTensor φ T P.complex Q.complex).hom ≫
          iB.hom at h
    simpa only [proEtaleScalarTensor, S, P, Q, E, iA, iB, cP, cQ, Category.assoc,
      CochainPullback.extend, CochainPullback.pull,
      CochainPullback.extensionPullback] using
      (tensorComparison_component S a P.iso Q.iso iA iB cP cQ
        (currentScalarCounit φ T (P.complex ⊗ Q.complex) ≫
          DerivedCategory.Q.map (scalarComplexTensor φ T P.complex Q.complex).hom)
        (by simpa only [Category.assoc] using h))
  refine ⟨⟨a, heq⟩, ?_⟩
  intro P Q hP hQ fP fQ
  have h := ha P Q ⟨hP, fP⟩ ⟨hQ, fQ⟩
  change S.map (RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T A) P Q (Or.inl hP)).hom ≫
      a.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (currentScalarCounit φ T P ⊗ₘ currentScalarCounit φ T Q) =
    currentScalarCounit φ T (P ⊗ Q) ≫
      DerivedCategory.Q.map (scalarComplexTensor φ T P Q).hom ≫
        (RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
          (ProEt.topology T) (proEtaleConstantRing T B)
            (E.obj P) (E.obj Q) (Or.inl (hE P ⟨hP, fP⟩))).hom at h
  rw [heq] at h
  let := RingedDerivedNative.lax.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B)
  have := RingedDerivedNative.isIso_mu.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B) (E.obj P) (E.obj Q)
      (Or.inl (hE P ⟨hP, fP⟩))
  have hh := congrArg (fun z ↦ z ≫ Functor.LaxMonoidal.μ DerivedCategory.Q
    (E.obj P) (E.obj Q)) h
  simpa only [RingedDerivedNative.tensorIso, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hh

set_option maxHeartbeats 2000000 in
-- Normalize several large functor and native tensor comparison expressions.
/-- Naturality and the normalized representative square imply the right-unit
law of the concrete scalar tensor comparison on every unbounded object.
Source: Stacks 06YS, 06YY, 07A4
(blueprint: lem-pur-scalar-right-unit-native).
Proof: use the tensor normalization at a chosen flat-term K-flat representative
and the coefficient unit. The unit normalization holds by construction. The
balanced cochain maps obey right unitality, so the representative transport lemma
proves the desired law on its localization. Both sides are natural in the
object, and the chosen representative is isomorphic to the original object.
Transport along that isomorphism and cancel its image.
-/
theorem proEtaleScalarTensor_rightUnit_of_normalized
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (a : tensor (proEtaleDerivedCategory T A) ⋙ scalarExtensionFunctor φ T ≅
      (scalarExtensionFunctor φ T).prod (scalarExtensionFunctor φ T) ⋙
        tensor (proEtaleDerivedCategory T B))
    (heq : ∀ K L, a.hom.app (K, L) = proEtaleScalarTensor φ T K L)
    (hnorm : ProEtaleScalarTensorNormalized φ T)
    (K : proEtaleDerivedCategory T A) :
    proEtaleScalarTensor φ T K (𝟙_ _) ≫
        ((scalarExtensionFunctor φ T).obj K ◁ proEtaleScalarUnit φ T) ≫
          (ρ_ ((scalarExtensionFunctor φ T).obj K)).hom =
      (scalarExtensionFunctor φ T).map (ρ_ K).hom := by
  let S := scalarExtensionFunctor φ T
  let E := CochainPullback.extend.{u + 1, u + 1, u}
    (proEtaleConstantRingMap (T := T) φ)
  let := RingedDerivedNative.lax.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T A)
  let := RingedDerivedNative.lax.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B)
  let α := scalarRightUnitMap S a (proEtaleScalarUnit φ T)
  let β : tensorRight (𝟙_ (proEtaleDerivedCategory T A)) ⋙ S ⟶ S :=
    Functor.whiskerRight (rightUnitorNatIso (proEtaleDerivedCategory T A)).hom S
  have hδ : ∀ X {Y Z : proEtaleDerivedCategory T A} (f : Y ⟶ Z),
      S.map (X ◁ f) ≫ a.hom.app (X, Z) =
        a.hom.app (X, Y) ≫ (S.obj X ◁ S.map f) := by
    intro X Y Z f
    have h := a.hom.naturality (Prod.mkHom (𝟙 X) f)
    change S.map (𝟙 X ⊗ₘ f) ≫ a.hom.app (X, Z) =
      a.hom.app (X, Y) ≫ (S.map (𝟙 X) ⊗ₘ S.map f) at h
    rw [S.map_id, id_tensorHom X, id_tensorHom (S.obj X)] at h
    exact h
  let P := scalarFlatRepresentative T K
  have hc := (CochainPullback.cochainComparison_monoidal.{u + 1, u + 1, u, u + 1, u}
    (CochainPullback.extensionPullback.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ))
    (CochainPullback.extensionComparison.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ))).2.2.2.2
      P.complex
  have ht := hnorm P.complex (𝟙_ (ScalarComplex T A)) P.kflat
    (scalarComplex_unit_kflat T) P.flat (scalarComplex_unit_flat T)
  have hμ := RingedDerivedNative.isIso_mu.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T A) P.complex (𝟙_ _) (Or.inl P.kflat)
  have ht' := congrArg (fun z ↦ S.map
    (Functor.LaxMonoidal.μ DerivedCategory.Q P.complex (𝟙_ _)) ≫ z) ht
  rw [← heq] at ht'
  have ht'' : a.hom.app (DerivedCategory.Q.obj P.complex, DerivedCategory.Q.obj (𝟙_ _)) ≫
      (currentScalarCounit φ T P.complex ⊗ₘ currentScalarCounit φ T (𝟙_ _)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (E.obj P.complex) (E.obj (𝟙_ _)) =
    S.map (Functor.LaxMonoidal.μ DerivedCategory.Q P.complex (𝟙_ _)) ≫
      currentScalarCounit φ T (P.complex ⊗ 𝟙_ _) ≫
        DerivedCategory.Q.map (scalarComplexTensor φ T P.complex (𝟙_ _)).hom := by
    dsimp only [RingedDerivedNative.tensorIso, Iso.symm_hom, asIso_inv] at ht'
    change S.map (Functor.LaxMonoidal.μ DerivedCategory.Q P.complex (𝟙_ _)) ≫
      S.map (inv (Functor.LaxMonoidal.μ DerivedCategory.Q P.complex (𝟙_ _))) ≫ _ = _ at ht'
    rw [← S.map_comp_assoc, IsIso.hom_inv_id, S.map_id, Category.id_comp] at ht'
    exact ht'
  let : IsIso ((currentScalarCounitNat φ T).app P.complex) :=
    currentScalarCounit_isIso φ T P.complex P.kflat
  have hp := rightUnit_at_representative DerivedCategory.Q DerivedCategory.Q E S
    (currentScalarCounitNat φ T) (fun X Y ↦ a.hom.app (X, Y))
    (proEtaleScalarUnit φ T) hδ P.complex
    (scalarComplexTensor φ T P.complex (𝟙_ _)).hom (scalarComplexUnit φ T).hom
    (by simpa only [E, scalarComplexUnit, scalarComplexTensor,
      CochainPullback.epsilon, CochainPullback.extend, CochainPullback.pull,
      id_tensorHom] using hc.symm) ht'' (proEtaleScalarUnit_normalized φ T)
  have hp' : α.app (DerivedCategory.Q.obj P.complex) =
      β.app (DerivedCategory.Q.obj P.complex) := hp
  rw [← heq]
  change α.app K = β.app K
  apply (cancel_epi ((tensorRight (𝟙_ _) ⋙ S).map P.iso.hom)).1
  rw [α.naturality, β.naturality, hp']

end AlgebraicGeometry.ProEtale
