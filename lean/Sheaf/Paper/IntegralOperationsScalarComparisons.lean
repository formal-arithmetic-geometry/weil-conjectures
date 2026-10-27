/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.Paper.IntegralOperationsScalarExtension
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralOperationsScalarComparisonModels

import all Sheaf.Paper.IntegralScalarPullbackChainProperties
import Sheaf.Paper.NormalizedIntegralScalarTensorComparison

import Sheaf.CategoryTheory.FunctorSquareRepresentativeDescent
import all Sheaf.Paper.IntegralScalarExtension
import Sheaf.Paper.CompletedIntegralFiniteFree
import Sheaf.Paper.NormalizedIntegralScalarCompletion
import Sheaf.Paper.NormalizedIntegralOrdinaryTensorChain
import Sheaf.Paper.IntegralScalarInternalHomComplete
import all Sheaf.Paper.ScalarExtensionComposition
import all Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import all Sheaf.Algebra.Homology.ScalarHomComparisonTower
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Normalized integral scalar comparisons

The finite-level maps, strict towers, and good-representative models are publicly
re-exported from IntegralOperationsScalarComparisonModels. This file retains the
ordinary derived comparisons, completed comparisons, and coherence statements.
(blueprint: lem-pur-integral-operations-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W


variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

section ScalarPullbackOrdinaryDescent

attribute [local semireducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor
attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsGoodLocalization integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor

/-- The ordinary scalar/pullback comparison is the localization of scalarPullbackChain.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the prescribed level generator maps are natural and commute with strict
reductions. The two Roos coordinates therefore give scalarPullbackChain. Finite
freeness commutes with countable products; cofinality of uniformizer filtrations
makes this chain map a quasi-isomorphism on good representatives. Localize the
map, conjugating by the two displayed representative comparisons. Good K-flat
resolutions compute all objects and roofs, giving naturality and invertibility.
The same localization property gives uniqueness with this normalization. -/
theorem scalarPullbackOrdinary_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f,
      scalarPullbackOrdinaryNormalization l E L ι f α := by
  let I := (integralOperationsGoodComplex l E Y).ι
  let q := integralOperationsGoodLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage I
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E Y
  let F := integralOrdinaryDerivedScalar l E L ι X
  let G := integralOrdinaryDerivedScalar l E L ι Y
  let S := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)
  let SX := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let k := (integralOperationsGoodComplex l L Y).lift (I ⋙ S)
    (fun P ↦ scalarGood l E L ι Y P)
  let p := integralOperationsGoodLocalization l L Y
  let t := I ⋙ integralOperationsPullbackComplexFunctor l E f
  let s := (integralOperationsGoodComplex l L Y).ι ⋙
    integralOperationsPullbackComplexFunctor l L f
  let eδ : t ⋙ SX ⋙ DerivedCategory.Q ≅ k ⋙ s ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      let := scalarPullbackChainQuasiIso l E L ι f P
      exact asIso (DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)))
      (by
        intro P Q a
        simpa only [Functor.comp_map,
          Functor.map_comp, I, SX, asIso_hom, ObjectProperty.ι_map,
          integralOperationsPullbackOnGood, k, ObjectProperty.lift, t, s,
          ObjectProperty.homMk_hom, Functor.comp_obj, ObjectProperty.ι_obj] using
          congrArg (fun z ↦ DerivedCategory.Q.map z)
            (scalarPullbackChain_naturality l E L ι f a.hom))
  let r : q ⋙ integralDerivedPullback l E f ≅ t ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ (integralDerivedPullbackComparison l E f).app P)
      (by
        intro P Q a
        simpa only [Functor.comp_map, integralOperationsPullbackOnGood, t, I,
          ObjectProperty.ι_map, Iso.app_hom] using
          (integralDerivedPullbackComparison l E f).hom.naturality a)
  let r' : p ⋙ integralDerivedPullback l L f ≅ s ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ (integralDerivedPullbackComparison l L f).app P)
      (by
        intro P Q a
        simpa only [Functor.comp_map, integralOperationsPullbackOnGood, s,
          ObjectProperty.ι_map, Iso.app_hom] using
          (integralDerivedPullbackComparison l L f).hom.naturality a)
  let η : q ⋙ G ≅ k ⋙ p :=
    NatIso.ofComponents
      (fun P ↦ (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.app P.obj)
      (by
        intro P Q a
        simpa only [Functor.comp_map, I, q, p, G, S,
          integralOperationsGoodLocalization, k, ObjectProperty.lift,
          ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.app_hom,
          Functor.comp_obj, ObjectProperty.ι_obj] using
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.naturality a.hom)
  change ∃! α : integralDerivedPullback l E f ⋙ F ≅ G ⋙ integralDerivedPullback l L f,
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      F.map (r.hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app (t.obj P) ≫
          eδ.hom.app P =
        α.hom.app (q.obj P) ≫ (integralDerivedPullback l L f).map (η.hom.app P) ≫
          r'.hom.app (k.obj P)
  exact functorSquareRepresentativeDescent q p k t s _ _
    (integralDerivedPullback l E f) (integralDerivedPullback l L f) SX F G
    (Localization.fullyFaithfulWhiskeringLeft q V
      (DerivedCategory (integralTowerModules l L X)))
    r r' (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors η eδ

end ScalarPullbackOrdinaryDescent

/-- The canonical localized scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackOrdinary {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f :=
  (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorOrdinaryNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩)

/-- The ordinary scalar/completed-tensor comparison has its full Roos normalization.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the finite tensor generator maps respect the signed total differential and
strict reductions. Their diagonal Roos map is scalarTensorChain. Finite freeness
commutes with its products, and the two uniformizer filtrations are cofinal. Thus
this map is a quasi-isomorphism on good pairs. Localize in both variables and
conjugate by the displayed comparisons. Roofs prove naturality and independence;
the universal property of the localization gives uniqueness. -/
theorem scalarTensorOrdinary_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W,
      scalarTensorOrdinaryNormalization l E L ι W α := by
  exact normalizedIntegralScalarTensorComparison l E L ι W

/-- The canonical localized scalar/completed-tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorOrdinary (W : AlgebraicGeometry.Scheme.{u}) :
    integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W :=
  (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarCompletionNormalization (W : AlgebraicGeometry.Scheme.{u})
    (χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W) : Prop :=
  (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K))


/-- The ordinary-to-completed scalar map is fixed on every good complex.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the already prescribed integralScalarCompletionChain has the quotient tensor
projection as its unshifted coordinate and zero shifted coordinate. Localize that
chain map using the scalar representative comparisons. Good resolutions compute
all objects and roofs, so the localization gives exactly one natural transformation.
The finite free basis commutes with the Roos products; on a complete input the
completion unit is invertible, which proves the second assertion. -/
theorem scalarCompletion_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      scalarCompletionNormalization l E L ι W χ := by
  exact normalizedIntegralScalarCompletion l E L ι W

/-- The normalized scalar completion map, including on nonconstructible complete Homs.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarCompletion (W : AlgebraicGeometry.Scheme.{u}) :
    integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W :=
  (scalarCompletion_existsUnique l E L ι W).exists.choose


/-- The intrinsic ordinary closed structure, retaining the recorded ambient Hom.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralClosed (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientClosedStructure (integralDerivedInternalHom l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralClosed

/-- The normalized total tensor models for the same closed structure.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralModels (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientTensorModels.{u, u+1, u, u+2}
      (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) (scalarIntegralClosed l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralTensorModel

attribute [local irreducible] scalarIntegralClosed scalarIntegralModels

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarOrdinaryTensorChainNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)

/-- Ordinary total tensor base change, fixed on sheafified pure tensors.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: send s tensor (x tensor y) to (s tensor x) tensor (1 tensor y).
Balance gives the inverse (s tensor x) tensor (t tensor y) to st tensor (x tensor y).
Sheafify, and sum over bidegrees. The formulas respect both signed differential
summands and chain maps. These generators determine the natural isomorphism. -/
theorem scalarOrdinaryTensorChain_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W),
      scalarOrdinaryTensorChainNormalization l E L ι W α := by
  exact normalizedIntegralOrdinaryTensorChain l E L ι W

/-- The pure-tensor-normalized ordinary total comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarOrdinaryTensorChain (W : AlgebraicGeometry.Scheme.{u}) :
    coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W) :=
  (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarClosedTensorNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
          (((scalarIntegralModels l E W).iso _ _ _ _ _ P.property.1 Q.property.1).hom) ≫
          α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (scalarIntegralClosed l L W).tensor.map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) =
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι W).hom.app (P.obj, Q.obj)) ≫
          ((scalarIntegralModels l L W).iso _ _ _ _ _
            (scalarGood l E L ι W P).1 (scalarGood l E L ι W Q).1).hom

section ScalarClosedTensorDescent

/-- The ordinary derived scalar tensor comparison is fixed on all good pairs.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: scalarGood supplies good target representatives. Localize the ordinary
pure-tensor chain isomorphism, using the two normalized closed tensor models.
Exact ordinary extension identifies its derived value with its termwise value.
The displayed square is that conjugation. Naturality on roofs and simultaneous
localization give a natural isomorphism and uniqueness with this square. -/
theorem scalarClosedTensor_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor,
      scalarClosedTensorNormalization l E L ι W α := by
  let I := (integralOperationsGoodComplex l E W).ι
  let q := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage I
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  let F := integralOrdinaryDerivedScalar l E L ι W
  let S := (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)
  let kE := ObjectProperty.ιOfLE
    (P := integralOperationsGoodComplex l E W)
    (P' := CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W)) (fun _ h ↦ h.1)
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (V.prod V)
    (DerivedCategory (integralTowerModules l L W))
  obtain ⟨α, hα, huniq⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q S F
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom
    (integralOperationsGoodComplex l E W)
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l L W))
    (fun P hP ↦ (scalarGood l E L ι W ⟨P, hP⟩).1) ff
    (coefficientTotalTensor (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientTotalTensor (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l L W))
    (scalarIntegralClosed l E W).tensor (scalarIntegralClosed l L W).tensor
    (by
      with_unfolding_all
        exact Functor.isoWhiskerLeft (kE.prod kE) (scalarIntegralModels l E W).comparison)
    (by
      with_unfolding_all exact (scalarIntegralModels l L W).comparison)
    (scalarOrdinaryTensorChain l E L ι W)
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  refine ⟨α, ?_, ?_⟩
  · unfold scalarClosedTensorNormalization
    intro P Q
    exact hα P.obj Q.obj P.property Q.property
  · intro β hβ
    apply huniq β
    intro P Q hP hQ
    exact hβ ⟨P, hP⟩ ⟨Q, hQ⟩

end ScalarClosedTensorDescent

/-- The canonical closed scalar tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarClosedTensor (W : AlgebraicGeometry.Scheme.{u}) :
    (scalarIntegralClosed l E W).tensor ⋙
        integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ (scalarIntegralClosed l L W).tensor :=
  (scalarClosedTensor_existsUnique l E L ι W).exists.choose

/-- Ordinary scalar/internal-Hom comparison: transpose of scalar-extended evaluation.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomOrdinary (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :
    (integralOrdinaryDerivedScalar l E L ι W).obj
        ((integralDerivedInternalHom l E W).obj (op M, N)) ⟶
      (integralDerivedInternalHom l L W).obj
        (op ((integralOrdinaryDerivedScalar l E L ι W).obj M),
          (integralOrdinaryDerivedScalar l E L ι W).obj N) :=
  coefficientBaseChangeHom (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) M N

section ScalarHomBaseChange

/-- Finite free scalar extension commutes with internal Hom, including unbounded inputs.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: resolve the second input by a K-injective complex. After restriction, finite
free extension is a finite direct sum. Internal Hom into a finite direct sum is
the corresponding finite sum of internal Homs; restriction is exact, so the derived
adjunction gives the same conclusion. Under the closed tensor model, the resulting
map is exactly the transpose of extended evaluation, namely scalarHomOrdinary.
The inverse is the finite-free tensor-Hom identity; its basis calculation is
independent of the basis. Thus this specified map is invertible. -/
theorem scalarHomOrdinary_isIso (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W)) :
    IsIso (scalarHomOrdinary l E L ι W M N) := by
  classical
  let J : GrothendieckTopology W.ProEt := AlgebraicGeometry.Scheme.ProEt.topology W
  let R : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted l E W
  let S : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted l L W
  let φ : R ⟶ S := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  have hobj : ∀ A, F.obj A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ A :=
    integralOrdinaryScalar_obj l E L ι W
  have hmap : ∀ {A B} (f : A ⟶ B), F.map f = eqToHom (hobj A) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ A f ≫ eqToHom (hobj B).symm := by
    intro A B f
    exact integralOrdinaryScalar_map l E L ι W f
  let D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} φ :=
    { E := F
      obj_eq := hobj
      map_eq := hmap
      preserves := by
        intro P Q f hP hQ hf
        let := hf
        infer_instance
      T := F.mapDerivedCategory
      pointwise := Functor.hasPointwiseLeftDerivedFunctor_of_inverts _
        (F.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso (.up ℤ))
      ε := F.mapDerivedCategoryFactors.hom
      universal := Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
      triangulated := ⟨inferInstance, inferInstance⟩
      computes := fun _ _ ↦ inferInstance }
  obtain ⟨κ, μ, hκ, hμ⟩ := ringedFiniteFreeHomBaseChange_tensor.{u + 1, u, u, u + 2}
    J φ D (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (scalarIntegralModels l E W) (scalarIntegralModels l L W)
  have hs (A : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (x : A.val.obj U) :
      ringedFiniteFreeScalarSection.{u + 1, u, u} J φ F hobj A U 1 x =
        integralOrdinaryTensorSection l E L ι W A U 1 x := by
    unfold ringedFiniteFreeScalarSection integralOrdinaryTensorSection
    have hη :=
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u,
        u + 1, u + 1} (J := J)
        (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ A)
    with_unfolding_all exact (congrArg ((eqToHom (hobj A).symm).val.app U)
      (ConcreteCategory.congr_hom (congr_app hη U) _))
  have hk : κ = scalarOrdinaryTensorChain l E L ι W := by
    apply (scalarOrdinaryTensorChain_existsUnique l E L ι W).unique
    · intro P Q p q U x y
      simpa only [D, hs] using hκ P Q p q U x y
    · exact (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose_spec
  have hm : μ = scalarClosedTensor l E L ι W := by
    apply (scalarClosedTensor_existsUnique l E L ι W).unique
    · intro P Q
      obtain ⟨hP, hQ, heq⟩ := hμ P.obj Q.obj P.property.1 Q.property.1
      simp only [D, hk, F, J, R, S, integralOrdinaryDerivedScalar] at heq ⊢
      exact heq
    · exact (scalarClosedTensor_existsUnique l E L ι W).exists.choose_spec
  let := ι.toAlgebra
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E W L ι φ
    (integralCompletedScalarMap_projection l E L ι W)
  have hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J R)
            (ULift.{u + 1} (Fin d))) := by
    let A := SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J R)
    let f : Fin (Module.finrank E L) → integralTowerModules l E W := fun _ ↦ A
    let : HasBiproduct f :=
      (Abelian.hasFiniteBiproducts (C := integralTowerModules l E W)).out _ |>.has_biproduct f
    with_unfolding_all
      exact ⟨Module.finrank E L, ⟨e ≪≫ biproductIso f ≪≫
        (Sigma.reindex (Equiv.ulift : ULift.{u + 1} (Fin (Module.finrank E L)) ≃ _)
          f).symm⟩⟩
  obtain ⟨α, hα⟩ := ringedFiniteFreeHomBaseChange_hom.{u + 1, u, u, u + 2}
    J φ hfree F hobj hmap inferInstance D.T D.ε D.universal
    (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (scalarIntegralModels l E W) (scalarIntegralModels l L W) κ μ hκ (by
      intro P Q hP hQ
      obtain ⟨hEP, hEQ, heq⟩ := hμ P Q hP hQ
      exact ⟨hEP, hEQ, D.computes P hP, D.computes Q hQ, heq⟩)
  have heq : scalarHomOrdinary l E L ι W M N = α.hom.app (op M, N) := by
    rw [hα M N, hm]
    rfl
  rw [heq]
  exact Iso.isIso_hom (α.app (op M, N))

end ScalarHomBaseChange

/-- The completion isomorphism on an actually derived-complete object.
Source: Bhatt--Scholze 3.5.1 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarCompletionIso (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules l E W)) (hK : IsSfDerivedComplete l E W K) :
    (integralOrdinaryDerivedScalar l E L ι W).obj K ≅
      (integralScalarExtension l E L ι W).obj K := by
  letI : IsIso ((scalarCompletion l E L ι W).app K) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 K hK
  exact asIso ((scalarCompletion l E L ι W).app K)

/-- Completed pullback/scalar comparison, conjugated by the normalized completion maps.
Source: Stacks 099N (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackCompleted {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : IsSfDerivedComplete l E Y K)
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj K)) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E f).obj K) ≅
      (integralDerivedPullback l L f).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarCompletionIso l E L ι X _ hF).symm ≪≫
    (scalarPullbackOrdinary l E L ι f).app K ≪≫
    (integralDerivedPullback l L f).mapIso (scalarCompletionIso l E L ι Y K hK)

/-- Completed tensor/scalar comparison, with the prescribed ordinary and Roos maps.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorCompleted (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hT : IsSfDerivedComplete l E W ((integralCompletedTensor l E W).obj (M, N))) :
    (integralScalarExtension l E L ι W).obj ((integralCompletedTensor l E W).obj (M, N)) ≅
      (integralCompletedTensor l L W).obj
        ((integralScalarExtension l E L ι W).obj M,
          (integralScalarExtension l E L ι W).obj N) :=
  (scalarCompletionIso l E L ι W _ hT).symm ≪≫
    (scalarTensorOrdinary l E L ι W).app (M, N) ≪≫
    (integralCompletedTensor l L W).mapIso
      (Iso.prod (scalarCompletionIso l E L ι W M hM) (scalarCompletionIso l E L ι W N hN))

/-- The completed Hom comparison uses the inverse first-variable comparison.
It is defined whenever its three completion inverses exist; in particular this
includes every permitted constructible-Hom pair in the owning definition.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomCompleted (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hH : IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N))) :
    (integralScalarExtension l E L ι W).obj
        ((integralDerivedInternalHom l E W).obj (op M, N)) ≅
      (integralDerivedInternalHom l L W).obj
        (op ((integralScalarExtension l E L ι W).obj M),
          (integralScalarExtension l E L ι W).obj N) := by
  letI := scalarHomOrdinary_isIso l E L ι W M N
  exact (scalarCompletionIso l E L ι W _ hH).symm ≪≫
    asIso (scalarHomOrdinary l E L ι W M N) ≪≫
    (integralDerivedInternalHom l L W).mapIso
      (Iso.prod (scalarCompletionIso l E L ι W M hM).symm.op
        (scalarCompletionIso l E L ι W N hN))


section ScalarHomCompleteness

/-- Ambient internal Hom into a complete object is complete; constructibility of the
Hom is not assumed. Source: Bhatt--Scholze 3.4.11; Stacks 08JB, 099B
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: restrict to every slice. Tensor-Hom currying identifies Hom from R[1/t]
into Hom(M,N) with Hom from M into Hom(R[1/t],N), which vanishes by completeness
of N. The local Koszul completion reflector identifies this vanishing with
invertibility of the canonical completion unit. Its Roos triangle is the specified
strict reduction-tower triangle, giving precisely IsSfDerivedComplete. -/
theorem scalarInternalHom_complete (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hN : IsSfDerivedComplete l E W N) :
    IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N)) := by
  exact integralScalarInternalHomComplete l E W M N hN

end ScalarHomCompleteness

/-- The canonical completed Hom comparison on all complete input pairs, including
those whose Hom is not constructible.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarHomCompleteInputs (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N) :=
  scalarHomCompleted l E L ι W M N hM hN (scalarInternalHom_complete l E W M N hN)


/-- Naturality of the evaluation-defined ordinary Hom comparison in both variables.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: uncurry both sides. Tensor-comparison naturality and evaluation naturality
identify both uncurried maps with extended evaluation after the two given arrows.
The closed transpose bijection gives the equality, including precomposition. -/
theorem scalarHomOrdinary_naturality (W : AlgebraicGeometry.Scheme.{u})
    (M N M' N' : DerivedCategory (integralTowerModules l E W))
    (a : M' ⟶ M) (b : N ⟶ N') :
    (integralOrdinaryDerivedScalar l E L ι W).map
      ((integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom a.op b)) ≫
        scalarHomOrdinary l E L ι W M' N' =
      scalarHomOrdinary l E L ι W M N ≫
        (integralDerivedInternalHom l L W).map (CategoryTheory.Prod.mkHom
          ((integralOrdinaryDerivedScalar l E L ι W).map a).op
          ((integralOrdinaryDerivedScalar l E L ι W).map b)) := by
  exact CategoryTheory.scalarBaseChangeHom_naturality (scalarIntegralClosed l E W)
    (scalarIntegralClosed l L W) (integralOrdinaryDerivedScalar l E L ι W)
    (scalarClosedTensor l E L ι W) M N M' N' a b

/-- The prescribed comparisons commute with coefficient towers before completion.
Conjugation by scalarCompletion gives the completed tower identities, with the
same completed scalar associators as the recorded scalar-extension composition.
Source: blueprint scalar comparison proof step 9; Stacks 07A4, 08J9
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: on finite pullback and tensor generators, both routes multiply the two
new coefficients in the same order. This gives equality of the strict tower maps
and both diagonal Roos coordinates. Their localizations give the first two
equalities. Uncurry the Hom equality: both routes evaluate h on m and multiply
those same coefficients. The normalized closed transpose gives the third
equality. The canonical completion maps commute with these diagrams by their
quotient generator normalization; cancel adjacent inverse completion maps to
obtain the completed identities. -/
theorem scalarOperationsOrdinary_tower
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{u}) :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalar l L F j X).map
          ((scalarPullbackOrdinary l E L ι f).hom.app K) ≫
        (scalarPullbackOrdinary l L F j f).hom.app
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) ≫
        (integralDerivedPullback l F f).map
          ((integralOrdinaryDerivedScalarComp l E L ι Y F j).hom.app K) =
      (integralOrdinaryDerivedScalarComp l E L ι X F j).hom.app
          ((integralDerivedPullback l E f).obj K) ≫
        (scalarPullbackOrdinary l E F (j.comp ι) f).hom.app K) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalar l L F j W).map
          ((scalarTensorOrdinary l E L ι W).hom.app (M, N)) ≫
        (scalarTensorOrdinary l L F j W).hom.app
          ((integralOrdinaryDerivedScalar l E L ι W).obj M,
            (integralOrdinaryDerivedScalar l E L ι W).obj N) ≫
        (integralCompletedTensor l F W).map (CategoryTheory.Prod.mkHom
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app M)
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
          ((integralCompletedTensor l E W).obj (M, N)) ≫
        (scalarTensorOrdinary l E F (j.comp ι) W).hom.app (M, N)) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalar l L F j W).map
          (scalarHomOrdinary l E L ι W M N) ≫
        scalarHomOrdinary l L F j W
          ((integralOrdinaryDerivedScalar l E L ι W).obj M)
          ((integralOrdinaryDerivedScalar l E L ι W).obj N) ≫
        (integralDerivedInternalHom l F W).map (CategoryTheory.Prod.mkHom
          (((integralOrdinaryDerivedScalarComp l E L ι W F j).inv.app M).op)
          ((integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app N)) =
      (integralOrdinaryDerivedScalarComp l E L ι W F j).hom.app
          ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
        scalarHomOrdinary l E F (j.comp ι) W M N) := by
  sorry

private theorem unit_of_idempotent
    {A : Type a} [Category.{b} A] {B : Type a'} [Category.{b'} B]
    (F : A ⥤ B) (T : A ⥤ A) (U : B ⥤ B)
    (u : T ≅ 𝟭 A) (v : U ≅ 𝟭 B) (α : F ⋙ U ≅ T ⋙ F)
    (h : ∀ X, U.map (α.hom.app X) ≫ α.hom.app (T.obj X) ≫
        F.map (u.hom.app (T.obj X)) =
      v.hom.app (U.obj (F.obj X)) ≫ α.hom.app X) :
    ∀ X, v.inv.app (F.obj X) ≫ α.hom.app X = F.map (u.inv.app X) := by
  have hu (X : A) : T.map (u.hom.app X) = u.hom.app (T.obj X) := by
    apply (cancel_mono (u.hom.app X)).mp
    exact u.hom.naturality (u.hom.app X)
  have hv (X : B) : U.map (v.hom.app X) = v.hom.app (U.obj X) := by
    apply (cancel_mono (v.hom.app X)).mp
    exact v.hom.naturality (v.hom.app X)
  have hfaith : U.Faithful := Functor.Faithful.of_iso v.symm
  let := hfaith
  intro X
  have h' : U.map (α.hom.app X ≫ F.map (u.hom.app X)) ≫ α.hom.app X =
      U.map (v.hom.app (F.obj X)) ≫ α.hom.app X := by
    have hn := α.hom.naturality (u.hom.app X)
    change U.map (F.map (u.hom.app X)) ≫ α.hom.app X =
      α.hom.app (T.obj X) ≫ F.map (T.map (u.hom.app X)) at hn
    rw [U.map_comp, Category.assoc, hn]
    simpa only [hu, hv] using h X
  have he : α.hom.app X ≫ F.map (u.hom.app X) = v.hom.app (F.obj X) :=
    U.map_injective ((cancel_mono (α.hom.app X)).mp h')
  apply (cancel_mono (F.map (u.hom.app X))).mp
  rw [Category.assoc, he, v.inv_hom_id_app, ← F.map_comp, u.inv_hom_id_app, F.map_id]
  rfl

/-- Identity coefficient extension has the ordinary tensor-unit normalization.
After completion this is the canonical completeness unit, rather than a literal
identity between chosen Roos representatives.
Source: blueprint scalar comparison proof step 9; Stacks 07A4, 08J9
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: specialize each pure-tensor formula to the identity coefficient map. The
ordinary unit multiplies r tensor x to rx, and its inverse sends x to 1 tensor x.
Both sides of each equation have this same action on generators. The strict Roos
maps and localization preserve these equalities. For Hom, uncurry and evaluate;
the inverse first-variable unit and the second-variable unit give the displayed
equation. Conjugating by the normalized completion maps gives the stated
canonical unit normalization on complete inputs. -/
theorem scalarOperationsOrdinary_unit {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{u}) :
    (∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalarUnit l E X).inv.app
          ((integralDerivedPullback l E f).obj K) ≫
        (scalarPullbackOrdinary l E E (AlgHom.id ℚ_[l] E) f).hom.app K =
      (integralDerivedPullback l E f).map
        ((integralOrdinaryDerivedScalarUnit l E Y).inv.app K)) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralOrdinaryDerivedScalarUnit l E W).inv.app
          ((integralCompletedTensor l E W).obj (M, N)) ≫
        (scalarTensorOrdinary l E E (AlgHom.id ℚ_[l] E) W).hom.app (M, N) =
      (integralCompletedTensor l E W).map (CategoryTheory.Prod.mkHom
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app M)
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app N))) ∧
    (∀ M N : DerivedCategory (integralTowerModules l E W),
      (integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom
          (((integralOrdinaryDerivedScalarUnit l E W).inv.app M).op) (𝟙 N)) ≫
        (integralOrdinaryDerivedScalarUnit l E W).inv.app
          ((integralDerivedInternalHom l E W).obj (op M, N)) ≫
        scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M N =
      (integralDerivedInternalHom l E W).map (CategoryTheory.Prod.mkHom
        (𝟙 (op ((integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) W).obj M)))
        ((integralOrdinaryDerivedScalarUnit l E W).inv.app N))) := by
  refine ⟨?_, ?_, ?_⟩
  · apply unit_of_idempotent (integralDerivedPullback l E f)
      (integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) Y)
      (integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) X)
      (integralOrdinaryDerivedScalarUnit l E Y) (integralOrdinaryDerivedScalarUnit l E X)
      (scalarPullbackOrdinary l E E (AlgHom.id ℚ_[l] E) f)
    intro K
    have h := (scalarOperationsOrdinary_tower l E E (AlgHom.id ℚ_[l] E)
      E (AlgHom.id ℚ_[l] E) f W).1 K
    simpa only [AlgHom.comp_id, ordinary_derived_target_unit] using h
  · let T := integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) W
    let e := integralOrdinaryDerivedScalarUnit l E W
    have h := unit_of_idempotent (integralCompletedTensor l E W) (T.prod T) T
      (NatIso.prod e e) e (scalarTensorOrdinary l E E (AlgHom.id ℚ_[l] E) W) ?_
    · intro M N
      exact h (M, N)
    · intro X
      obtain ⟨M, N⟩ := X
      have h' := (scalarOperationsOrdinary_tower l E E (AlgHom.id ℚ_[l] E)
        E (AlgHom.id ℚ_[l] E) (𝟙 W) W).2.1 M N
      simpa only [T, e, NatIso.prod, NatTrans.prod, Functor.prod_obj,
        AlgHom.comp_id, ordinary_derived_target_unit] using h'
  · let T := integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) W
    let e := integralOrdinaryDerivedScalarUnit l E W
    let H := integralDerivedInternalHom l E W
    let α : H ⋙ T ≅ T.op.prod T ⋙ H := NatIso.ofComponents
      (fun X ↦ by
        let := scalarHomOrdinary_isIso l E E (AlgHom.id ℚ_[l] E) W X.1.unop X.2
        exact asIso (scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W X.1.unop X.2))
      (by
        intro X Y f
        exact scalarHomOrdinary_naturality l E E (AlgHom.id ℚ_[l] E) W
          X.1.unop X.2 Y.1.unop Y.2 f.1.unop f.2)
    have hcInv (K : DerivedCategory (integralTowerModules l E W)) :
        (integralOrdinaryDerivedScalarComp l E E (AlgHom.id ℚ_[l] E) W
          E (AlgHom.id ℚ_[l] E)).inv.app K = e.inv.app (T.obj K) := by
      have hc : (integralOrdinaryDerivedScalarComp l E E (AlgHom.id ℚ_[l] E) W
          E (AlgHom.id ℚ_[l] E)).app K = e.app (T.obj K) :=
        Iso.ext (ordinary_derived_target_unit l E E (AlgHom.id ℚ_[l] E) W K)
      exact congrArg Iso.inv hc
    have h := unit_of_idempotent H (T.op.prod T) T (NatIso.prod (NatIso.op e.symm) e) e α ?_
    · intro M N
      have h' := h (Opposite.op M, N)
      change e.inv.app (H.obj (Opposite.op M, N)) ≫
          scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M N =
        H.map (CategoryTheory.Prod.mkHom (e.hom.app M).op (e.inv.app N)) at h'
      change H.map (CategoryTheory.Prod.mkHom (e.inv.app M).op (𝟙 N)) ≫
          e.inv.app (H.obj (Opposite.op M, N)) ≫
            scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M N =
        H.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (T.obj M))) (e.inv.app N))
      rw [h', ← H.map_comp]
      congr 1
      ext <;> simp [← CategoryTheory.op_comp]
      rfl
    · intro X
      obtain ⟨M, N⟩ := X
      have h' := (scalarOperationsOrdinary_tower l E E (AlgHom.id ℚ_[l] E)
        E (AlgHom.id ℚ_[l] E) (𝟙 W) W).2.2 M.unop N
      change T.map (scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M.unop N) ≫
          scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W (T.obj M.unop) (T.obj N) ≫
          H.map (CategoryTheory.Prod.mkHom (e.inv.app (T.obj M.unop)).op
            (e.hom.app (T.obj N))) =
        e.hom.app (T.obj (H.obj (M, N))) ≫
          scalarHomOrdinary l E E (AlgHom.id ℚ_[l] E) W M.unop N
      simpa only [T, e, H, AlgHom.comp_id, ordinary_derived_target_unit, hcInv] using h'

end WeilConjectures
