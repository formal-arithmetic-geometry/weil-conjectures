/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.SfIntegralConstructibleTriangulated
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Sheaf.Paper.CompletedCoefficientPushforwardModels
public import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.CompletedCoefficientDirectImageDiagrams
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
import Sheaf.CategoryTheory.LinearRightAdjoint
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas
import Sheaf.Paper.SfCompleteDirectImageReduction
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.KoszulReconstruction

/-! # Ordinary completed-ring realization of integral recollement

Source: Weil blueprint, main-20261015, smooth-purity localization, Integral stage
(blueprint: lem-sf-integral-ordinary-recollement-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary completed-coefficient direct image is a right adjoint.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the canonical completed structural map defines a morphism of ringed topoi.
Its module tensor inverse image is left adjoint to the specified module direct image. -/
@[instance] theorem sfOrdinaryModulePush_isRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfCompletedModuleDirectImage l E f).IsRightAdjoint := by
  sorry

/-- The actual ordinary tensor inverse image, as Mathlib's left adjoint to the
specified completed-coefficient module direct image.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryModulePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarReductionSource l E Y ⥤ scalarReductionSource l E X :=
  (sfCompletedModuleDirectImage l E f).leftAdjoint

/-- The ordinary module adjunction, retaining its unit and counit.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfOrdinaryModulePull l E f ⊣ sfCompletedModuleDirectImage l E f :=
  Adjunction.ofIsRightAdjoint (sfCompletedModuleDirectImage l E f)

/-- Additivity of ordinary tensor inverse image.
Source: Stacks 03D2; localization proof step 1
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the module inverse-image adjunction is additive: its tensor and sheafification
constructions preserve addition of module maps. -/
@[instance] theorem sfOrdinaryModulePull_additive
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (sfOrdinaryModulePull l E f).Additive := by
  sorry

/-- Exactness of ordinary immersion inverse image, with completed coefficients.
Source: Stacks 09AA, 099N; localization proof steps 1--2
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the canonical coefficient inverse-image isomorphism commutes with each finite
projection. Immersion inverse image is exact, and coefficient transport is exact. -/
@[instance] theorem sfOrdinaryModulePull_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    PreservesFiniteLimits (sfOrdinaryModulePull l E f) := by
  sorry

/-- Ordinary inverse image preserves finite colimits.
Source: Stacks 03D2; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the specified functor is a left adjoint and therefore preserves colimits. -/
@[instance] theorem sfOrdinaryModulePull_preservesFiniteColimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (sfOrdinaryModulePull l E f) := by
  sorry

/-- Exact descent of ordinary immersion pullback.
Source: Stacks 06YY; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
  (sfOrdinaryModulePull l E f).mapDerivedCategory

/-- Ordinary unbounded pullback/direct-image adjunction.
Source: Stacks 07A6; localization proof step 5
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryDerivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    sfOrdinaryDerivedPull l E f ⊣ sfCompletedDerivedDirectImage l E f :=
  (sfOrdinaryModuleAdjunction l E f).mapDerivedCategoryRightDerivedAdjunction

/-- The ordinary support kernel followed by closed inverse image. This is the
completed-coefficient specialization of ringedClosedKernelShriek, expressed after
canonical identification of inverse-image coefficients with the completed rings.
Source: Stacks 09AH; localization proof steps 8--9
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryClosedKernel {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    scalarReductionSource l E X ⥤ scalarReductionSource l E Z :=
  kernel (sfOrdinaryModuleAdjunction l E j).unit ⋙ sfOrdinaryModulePull l E i

/-- The support kernel functor is additive.
Source: Stacks 09AH; localization proof step 8
(blueprint: lem-sf-integral-ordinary-recollement-realization).
Proof: the open unit is an additive natural transformation. Kernels in the additive
functor category are additive, and closed inverse image is additive. -/
@[instance] theorem sfOrdinaryClosedKernel_additive
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    (sfOrdinaryClosedKernel l E i j).Additive := by
  sorry

/-- The ambient, unbounded ordinary kernel adjoint, computed by K-injectives.
Source: Stacks 09AA, 09AH; localization proof step 8
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryClosedShriek {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Z) :=
  (sfOrdinaryClosedKernel l E i j).rightDerivedFunctor

/-- The canonical ordinary finite-reduction adjunct of a direct image.
Source: Stacks 07A6; localization proof steps 3--4
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPushReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
      ((sfCompletedDerivedDirectImage l E f).obj K) ⟶ sfFiniteDerivedDirectImage l E f K n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    ((sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The actual nth strict Roos projection, before localization.
Source: Stacks 08TC; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullRoosProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
    integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) ⟶
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism
      (K := fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m))
      (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P.obj))) ≫
    Pi.π (fun m : ℕ ↦
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m)) n

/-- The homotopy coordinate of the strict Roos complex.
Source: Stacks 08TC; localization proof step 2
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullRoosZeroCoordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (q : ℤ) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism
      (K := fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op m))
      (integralOperationsTowerStep
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)))).v q (q - 1) (by omega)

/-- The canonical quotient-augmentation leg, transposed through the ordinary
pullback adjunction. This is reduction unit followed by the finite pullback unit,
with the scalar-restriction/direct-image comparison in its specified direction.
Source: localization proof steps 2 and 5; Stacks 03D2, 07A6
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryPullAugmentationLeg {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (q : ℤ) :
    P.obj.X q ⟶ (sfCompletedModuleDirectImage l E f).obj
      ((((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op n)).X q) :=
  (scalarReductionExtension_adjunction l E Y n).choose.unit.app (P.obj.X q) ≫
            (scalarReductionRestriction l E Y n).map
              ((coefficientProEtaleModuleAdjunction.{u, u} f
                (CommRingCat.of
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
                    ((scalarReductionExtension l E Y n).obj (P.obj.X q))) ≫
            (sfDirectImageRestrictionComparison l E f n).hom.app
              ((integralOperationsLevelPullback l E f n).obj
                ((scalarReductionExtension l E Y n).obj (P.obj.X q)))

attribute [local irreducible] sfOrdinaryModulePull sfCompletedModuleDirectImage
  sfCompletedCoefficientMap integralDerivedPullback
  sfOrdinaryDerivedAdjunction
  integralOperationsPullbackTowerFunctor sfOrdinaryPullRoosProjection
  sfOrdinaryPullRoosZeroCoordinate sfOrdinaryPullAugmentationLeg

/-- Normalized comparisons for one immersion, in the actual completed and finite
module categories. All positive exponents occur as n+1. The representative equation
specifies the whole Roos augmentation, including its zero homotopy coordinate.
Source: localization Integral stage, proof steps 2--7
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
structure SfOrdinaryIntegralComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] where
  diagrams : CompletedCoefficientPushforward.ComparisonData l E f
  diagrams_structure : diagrams.structureMap =
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sfCompletedCoefficientMap l E f)
  diagrams_model : diagrams.completedImage.functor ≅ sfCompletedDerivedDirectImage l E f
  diagrams_unit : ∀ I : CochainComplex (scalarReductionSource l E X) ℤ,
    HEq (diagrams.completedImage.unit.app I ≫
      diagrams_model.hom.app (DerivedCategory.Q.obj I))
      ((derivedCochainRightUnit (sfCompletedModuleDirectImage l E f)
        (sfCompletedDerivedDirectImage l E f)
        (sfCompletedModuleDirectImage l E f).rightDerivedFunctorUnit).app I)
  pull : sfOrdinaryDerivedPull l E f ⟶ integralDerivedPullback l E f
  pull_complete : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    IsSfDerivedComplete l E Y K → IsIso (pull.app K)
  pull_preserves_complete : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    IsSfDerivedComplete l E Y K →
      IsSfDerivedComplete l E X ((sfOrdinaryDerivedPull l E f).obj K)
  pull_model : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ a : ((sfOrdinaryModulePull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj ⟶
        integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P.obj),
      pull.app (DerivedCategory.Q.obj P.obj) ≫
          (integralDerivedPullbackComparison l E f).hom.app P =
        (sfOrdinaryModulePull l E f).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map a ∧
      (∀ (n : ℕ) (q : ℤ),
        (sfOrdinaryModuleAdjunction l E f).homEquiv _ _
          ((a ≫ sfOrdinaryPullRoosProjection l E f P n).f q) =
            sfOrdinaryPullAugmentationLeg l E f P n q) ∧
      (∀ q : ℤ, a.f q ≫ (sfOrdinaryPullRoosZeroCoordinate l E f P q) = 0)
  push : ∀ (K : DerivedCategory (scalarReductionSource l E X)),
    sfIntegralConstructible l E X K →
    ∀ [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K),
      (sfCompletedDerivedDirectImage l E f).obj K ≅ L.obj
  push_projection : ∀ (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ),
    (push K hK L).hom ≫ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n =
      (sfCompletedDerivedDirectImage l E f).map ((sfDerivedReductionUnit l E X n).app K) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)
  push_reduction : ∀ (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) (n : ℕ),
    IsIso (sfDirectImageReductionComparison l E f L n) ∧
      (scalarReductionDerivedExtension l E Y n).map (push K hK L).hom ≫
        sfDirectImageReductionComparison l E f L n = sfOrdinaryPushReduction l E f K n
  push_constructible : ∀ K : DerivedCategory (scalarReductionSource l E X),
    sfIntegralConstructible l E X K →
      sfIntegralConstructible l E Y ((sfCompletedDerivedDirectImage l E f).obj K)
  pull_constructible : ∀ K : DerivedCategory (scalarReductionSource l E Y),
    sfIntegralConstructible l E Y K →
      sfIntegralConstructible l E X ((sfOrdinaryDerivedPull l E f).obj K) ∧
      sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K)

  pull_reduction : ∀ (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : sfIntegralConstructible l E Y K)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K) (n : ℕ),
    IsIso (integralPullbackFiniteComparison l E f K P e n)
  pull_interval : ∀ (K : DerivedCategory (scalarReductionSource l E Y))
    (a b : ℤ), a ≤ b → sfIntegralConstructible l E Y K →
    (∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E Y n).obj K) ⊆ Set.Icc a b) →
    ∀ n : ℕ, proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension l E X n).obj
        ((sfOrdinaryDerivedPull l E f).obj K)) ⊆ Set.Icc a b

/-- Restriction of ordinary direct image to the precise integral constructible category.
Source: localization proof step 6
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def SfOrdinaryIntegralComparison.pushFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (C : SfOrdinaryIntegralComparison l E f) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E X).ι ⋙ sfCompletedDerivedDirectImage l E f)
    (fun K ↦ C.push_constructible K.obj K.property)

/-- Restriction of the specified completed pullback, with its unchanged object and map.
Source: localization proof steps 2 and 5
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def SfOrdinaryIntegralComparison.pullFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (C : SfOrdinaryIntegralComparison l E f) :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f)
    (fun K ↦ (C.pull_constructible K.obj K.property).2)

/-- Unit and counit normalization of the completed adjunction after ordinary realization.
The direct image is its ordinary model; push_projection and push_reduction identify
this same functor with every specified strict-tower direct image.
Source: localization proof step 5
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def SfOrdinaryIntegralComparison.AdjunctionNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (C : SfOrdinaryIntegralComparison l E f)
    (a : C.pullFunctor l E f ⊣ C.pushFunctor l E f) : Prop :=
  (∀ K : sfIntegralConstructibleCategory l E Y,
    (a.unit.app K).hom = (sfOrdinaryDerivedAdjunction l E f).unit.app K.obj ≫
      (sfCompletedDerivedDirectImage l E f).map (C.pull.app K.obj)) ∧
  (∀ N : sfIntegralConstructibleCategory l E X,
    C.pull.app ((sfCompletedDerivedDirectImage l E f).obj N.obj) ≫
      (a.counit.app N).hom = (sfOrdinaryDerivedAdjunction l E f).counit.app N.obj)

/-- The literal restriction of the ambient kernel adjoint, once its preservation
property is known. Object and arrow maps are inherited without a new choice.
Source: localization Integral stage, proof step 11
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
def sfOrdinaryConstructibleShriek {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (h : ∀ K : DerivedCategory (scalarReductionSource l E X),
      sfIntegralConstructible l E X K →
        sfIntegralConstructible l E Z ((sfOrdinaryClosedShriek l E i j).obj K)) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Z :=
  (sfIntegralConstructible l E Z).lift
    ((sfIntegralConstructible l E X).ι ⋙ sfOrdinaryClosedShriek l E i j)
    (fun K ↦ h K.obj K.property)

/-- The complete ordinary realization, including the actual ambient kernel right
adjoint, its constructible restriction, and its counit/open-unit supported triangle.
Source: localization Integral stage, proof steps 8--12
(blueprint: lem-sf-integral-ordinary-recollement-realization). -/
structure SfIntegralOrdinaryRecollement {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  closed : SfOrdinaryIntegralComparison l E i
  opened : SfOrdinaryIntegralComparison l E j
  closedAdjunction : closed.pullFunctor l E i ⊣ closed.pushFunctor l E i
  openAdjunction : opened.pullFunctor l E j ⊣ opened.pushFunctor l E j
  closed_normalized : closed.AdjunctionNormalized l E i closedAdjunction
  open_normalized : opened.AdjunctionNormalized l E j openAdjunction
  kernelAdjunction : sfCompletedModuleDirectImage l E i ⊣ sfOrdinaryClosedKernel l E i j
  kernel_counit :
    Functor.whiskerLeft (kernel (sfOrdinaryModuleAdjunction l E j).unit)
        (sfOrdinaryModuleAdjunction l E i).unit ≫ kernelAdjunction.counit =
      kernel.ι (sfOrdinaryModuleAdjunction l E j).unit
  ambientAdjunction : sfCompletedDerivedDirectImage l E i ⊣ sfOrdinaryClosedShriek l E i j
  ambient_counit : ∀ (I : CochainComplex (scalarReductionSource l E X) ℤ)
    [I.IsKInjective],
    (derivedCochainRightUnit (sfCompletedModuleDirectImage l E i)
        (sfCompletedDerivedDirectImage l E i)
        (sfCompletedModuleDirectImage l E i).rightDerivedFunctorUnit).app
          (((sfOrdinaryClosedKernel l E i j).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (sfCompletedDerivedDirectImage l E i).map
        ((sfOrdinaryClosedKernel l E i j).rightDerivedFunctorObjQIso I).inv ≫
      ambientAdjunction.counit.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((kernelAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)
  shriek_constructible : ∀ K : DerivedCategory (scalarReductionSource l E X),
    sfIntegralConstructible l E X K →
      sfIntegralConstructible l E Z ((sfOrdinaryClosedShriek l E i j).obj K)
  restrictedAdjunction : closed.pushFunctor l E i ⊣
    sfOrdinaryConstructibleShriek l E i j shriek_constructible
  restricted_unit : ∀ P : sfIntegralConstructibleCategory l E Z,
    (restrictedAdjunction.unit.app P).hom = ambientAdjunction.unit.app P.obj
  restricted_counit : ∀ K : sfIntegralConstructibleCategory l E X,
    (restrictedAdjunction.counit.app K).hom = ambientAdjunction.counit.app K.obj
  shriek_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    (sfOrdinaryConstructibleShriek l E i j shriek_constructible)
  closed_shift : (closed.pushFunctor l E i).CommShift ℤ
  closed_shift_normalization : ∀ (n : ℤ) (P : sfIntegralConstructibleCategory l E Z),
    ((Functor.commShiftIso (closed.pushFunctor l E i) (self := closed_shift) n).hom.app
        P).hom ≫ ((sfIntegralConstructible l E X).ι.commShiftIso n).hom.app
          ((closed.pushFunctor l E i).obj P) =
      (sfCompletedDerivedDirectImage l E i).map
          (((sfIntegralConstructible l E Z).ι.commShiftIso n).hom.app P) ≫
        ((sfCompletedDerivedDirectImage l E i).commShiftIso n).hom.app P.obj
  shriek_shift : (sfOrdinaryConstructibleShriek l E i j shriek_constructible).CommShift ℤ
  shriek_shift_adjunction : @Adjunction.CommShift _ _ _ _ _ _ restrictedAdjunction ℤ _ _ _
    closed_shift shriek_shift
  shriek_exact : ∀ T : Triangle (sfIntegralConstructibleCategory l E X),
    T ∈ distTriang _ →
    (@Functor.mapTriangle _ _ _ _ _ _
      (sfOrdinaryConstructibleShriek l E i j shriek_constructible) shriek_shift).obj T ∈
      distTriang _
  supported_triangle : ∀ (K : DerivedCategory (scalarReductionSource l E X))
    (_hK : sfIntegralConstructible l E X K),
    ∃ δ : (sfCompletedDerivedDirectImage l E j).obj
        ((sfOrdinaryDerivedPull l E j).obj K) ⟶
      ((sfCompletedDerivedDirectImage l E i).obj
        ((sfOrdinaryClosedShriek l E i j).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (ambientAdjunction.counit.app K)
        ((sfOrdinaryDerivedAdjunction l E j).unit.app K) δ ∈ distTriang _ ∧
      sfIntegralConstructible l E X
        ((sfCompletedDerivedDirectImage l E i).obj
          ((sfOrdinaryClosedShriek l E i j).obj K)) ∧
      sfIntegralConstructible l E X
        ((sfCompletedDerivedDirectImage l E j).obj
          ((sfOrdinaryDerivedPull l E j).obj K))
  closed_unit : ∀ P : sfIntegralConstructibleCategory l E Z,
    IsIso (closedAdjunction.counit.app P)
  open_unit : ∀ G : sfIntegralConstructibleCategory l E U,
    IsIso (openAdjunction.counit.app G)
  disjoint : ∀ P : sfIntegralConstructibleCategory l E Z,
    IsZero ((opened.pullFunctor l E j).obj ((closed.pushFunctor l E i).obj P))
  orthogonal : ∀ (P : sfIntegralConstructibleCategory l E Z)
    (G : sfIntegralConstructibleCategory l E U) (m : ℤ),
    Subsingleton ((((closed.pushFunctor l E i).obj P)⟦m⟧) ⟶
      (opened.pushFunctor l E j).obj G)
  conservative : ∀ (T : Scheme.{u}) (K L : sfIntegralConstructibleCategory l E T)
    (a : K ⟶ L),
    (∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E T n).map a.hom)) → IsIso a

/-- Ordinary completed-ring recollement realizes all specified integral operations.

Source: Weil blueprint main-20261015, prop-sf-localization-all-stages, Integral stage
(blueprint: lem-sf-integral-ordinary-recollement-realization).

Proof plan (the thirteen steps of the node):
1. The valuation ring is a DVR with finite residue field. Positive quotients have
   the two-term free resolutions. Finite-type schemes over a field are Noetherian;
   their open complements are quasi-compact. Profinite coefficient inverse image
   identifies the completed rings and all finite projections.
2. Apply the immersion-completed-pullback comparison to i and j. Use one flat-term
   K-flat representative and its strict quotient tower. Exact countable products
   and strictRoosComparison identify the product-cone and total-derived-limit models,
   including every projection and the augmentation with zero homotopy coordinate.
3. The Roos/intrinsic-completeness equivalence reconstructs a complete K from its
   canonical quotient augmentation. Apply directImageRlimIso to this strict tower.
   The scalar-restriction comparisons, normalized on K-injectives, identify its
   terms with Res_n Rf_n K_n. Derived pushforward composition identifies transitions
   before evaluation and carries the completion unit to the same augmentation.
4. sfCompleteDirectImage_reduction makes the adjunct of each actual projection
   invertible in the actual finite module category. Its scalar-extension adjunction
   gives push_reduction. This is compatible with every quotient transition.
5. Restrict the ordinary adjunction to complete objects and use the completion
   reflector. Its unit is Rf_ord(c) eta_ord; its counit satisfies eps_comp c = eps_ord.
   The completed-coefficient direct-image diagrams retain the finite quotient units,
   evaluations and universal-unit normalization. Conjugate by the strict push comparison.
6. Integral direct-image constructibility applies over any field with l invertible.
   It gives completeness, each constructible finite reduction and a common interval.
   Ordinary images inherit these through the comparison; pullbacks use step 2.
7. Tensor 0 -> A_1 -> A_n -> A_(n-1) -> 0 with the same flat-term representative.
   Exact derived direct image and the ring-change comparisons give triangles of
   restricted finite images. The homology long exact sequence propagates one interval
   from n=1 to all n. No finite-Tor subcategory is substituted.
8. Apply proEtale_ringed_closed_kernel_adjoint over the completed ring. Its ordinary
   adjunctions give i* i_* = 1, j* Rj_* = 1, j* i_* = 0 and Hom orthogonality in
   every integer shift. Step 5 identifies their maps on the constructible categories.
9. Complete the actual open unit K -> Rj_*j*K to a distinguished fibre triangle.
   Exact j* kills the fibre. The closed-essential-image theorem identifies the
   fibre with i_*Q, for Q=i*F. Isomorphism and extension closure of the integral
   constructible predicate show that F and Q are integral constructible.
10. Shifted Hom orthogonality makes Hom(i_*P,F) -> Hom(i_*P,K) bijective. Closed
    full faithfulness identifies this with Hom(P,Q). The orthogonal-counit theorem
    identifies this triangle, including its first arrow, with the ambient kernel
    adjoint's counit triangle.
11. Thus the actual ambient right adjoint restricts to the precise full integral
    subcategory. The first two arrows are the exceptional counit and open unit.
12. The linear-right-adjoint theorem makes the restriction R-linear. The adjunction
    shift structure and triangulated-right-adjoint theorem give exactness with
    precisely the shift structure induced by adjunction.
13. The cone of a morphism invertible at every reduction is complete with zero
    reductions. Its canonical augmented Roos triangle makes the cone zero, hence
    the morphism is invertible. Empty open/closed pieces and zero inputs are included. -/
theorem sfIntegralOrdinaryRecollement_realization
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {Z U X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hU : Set.range j = (Set.range i)ᶜ) :
    Nonempty (SfIntegralOrdinaryRecollement l E i j) := by
  sorry

end WeilConjectures
