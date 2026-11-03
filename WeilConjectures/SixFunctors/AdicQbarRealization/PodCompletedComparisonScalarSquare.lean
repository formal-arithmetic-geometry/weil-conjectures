/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
import WeilConjectures.SixFunctors.AdicQbarRealization.PodCompletedComparisonNormalization
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization

/-! # Scalar compatibility of the actual completion comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(4), Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-pod-completed-comparison-scalar-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

attribute [local implicit_reducible] integralScalarExtensionOfUniverses

/-- Scalar extension commutes with the actual completion-unit pullback comparison.
Source: BS Lemma 6.5.9(4), Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-pod-completed-comparison-scalar-square).

Proof: identify each actual comparison with the normalized inverse-image comparison.
Use the existing scalar-extension square for that comparison. The counit-normalized
scalar model identifies its completion map with scalarCompletion. Cancel its
invertible exact-model component on the complete inverse-image object. Naturality
moves these model changes across the comparison, and the inverse coefficient-map
presentation changes cancel. This gives the specified completedScalarReindex map. -/
theorem completion_scalar_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    (completedDerivedScalarExtension l E L i X).map (podCompletedToTower l E g K.obj) ≫
        (completedScalarComparison l E L i X).app
          ((integralDerivedPullback l E g).obj K.obj) ≫
        (integralPullbackScalarComparison l E L i g K).hom.hom =
      (completedScalarReindex l E L i g).hom.app K.obj ≫
        (podCompletedDerivedInverseImage l L g).map
          ((completedScalarComparison l E L i Y).app K.obj) ≫
        podCompletedToTower l L g ((integralScalarExtension l E L i Y).obj K.obj) := by
  have h := isomorphismComparison_scalarExtension l E L i g hX hY K.obj K.property
  have hχ (W : Scheme.{u}) (A : DerivedCategory (integralTowerModules l E W)) :
      (scalarExactModel l E L i W).hom.app A ≫
          (completedScalarComparison l E L i W).app A =
        (scalarCompletion l E L i W).app A :=
    congrArg (fun t ↦ t.app A)
      (isomorphismScalarModel_existsUnique l E L i W).exists.choose_spec.2
  let κ := AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l E g hX hY K.obj
  let eX := scalarExactModel l E L i X
  let eY := scalarExactModel l E L i Y
  let cE := completedReindexModel l E g
  let cL := completedReindexModel l L g
  let χX := completedScalarComparison l E L i X
  let χY := completedScalarComparison l E L i Y
  let N := isomorphismScalarTensorDerived l E L i g
  let α := (integralPullbackScalarComparison l E L i g K).hom.hom
  let κL := AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l L g hX hY
    ((integralScalarExtension l E L i Y).obj K.obj)
  let NK := (AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E g).obj K.obj
  let hNK := (isomorphismComparisonInputs_constructible l E g hX hY K.obj K.property).1.1
  have hc : χX.app NK ≫ (scalarCompletionIso l E L i X NK hNK).inv =
      eX.inv.app NK := by
    apply (cancel_epi (eX.hom.app NK)).1
    erw [← Category.assoc, hχ]
    change (scalarCompletionIso l E L i X NK hNK).hom ≫ _ = _
    exact (scalarCompletionIso l E L i X NK hNK).hom_inv_id.trans (eX.hom_inv_id_app NK).symm
  change (integralScalarExtension l E L i X).map κ ≫ α = _ at h
  have hnχ := χX.naturality κ
  have hnX := eX.inv.naturality (cE.hom.app K.obj)
  have hnL := cL.inv.naturality ((scalarCompletion l E L i Y).app K.obj)
  try dsimp only [Functor.comp_map] at hnχ
  try dsimp only [Functor.comp_map] at hnX
  try dsimp only [Functor.comp_map] at hnL
  have hκ : (completedDerivedScalarExtension l E L i X).map κ ≫
      χX.app ((integralDerivedPullback l E g).obj K.obj) ≫ α =
      eX.inv.app NK ≫ N.hom.app K.obj ≫
        (AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l L g).map
          ((scalarCompletion l E L i Y).app K.obj) ≫ κL := by
    erw [reassoc_of% hnχ, h]
    dsimp only [isomorphismComparisonScalarBeta]
    simp only [Category.assoc]
    erw [← Category.assoc (χX.app NK), hc]
    rfl
  erw [podCompletedComparison_normalization l E g hX hY,
    podCompletedComparison_normalization l L g hX hY, Functor.map_comp]
  simp only [Category.assoc]
  erw [hκ, ← Category.assoc _ (eX.inv.app NK), hnX]
  have hb : (completedScalarReindex l E L i g).hom.app K.obj =
      eX.inv.app ((podCompletedDerivedInverseImage l E g).obj K.obj) ≫
        (integralOrdinaryDerivedScalar l E L i X).map (cE.hom.app K.obj) ≫
        N.hom.app K.obj ≫
        cL.inv.app ((integralOrdinaryDerivedScalar l E L i Y).obj K.obj) ≫
        (podCompletedDerivedInverseImage l L g).map (eY.hom.app K.obj) := by rfl
  erw [hb]
  simp only [Category.assoc]
  erw [← (podCompletedDerivedInverseImage l L g).map_comp_assoc, hχ]
  erw [← reassoc_of% hnL]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The actual completion square expressed with its constructible component isomorphisms.
Source: BS Lemma 6.5.9(4) and Remark 6.8.15.
(blueprint: lem-pod-completed-comparison-scalar-square).
Proof: apply completion_scalar_square and expose only the full-subcategory object
maps and the two identical universal derived scalar-extension presentations. -/
theorem completion_constructible_scalar_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (i : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    let KL := (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y).obj K
    let KE := (constructibleIntegralPullback l E g).obj K
    let δ := (integralPullbackScalarComparison l E L i g K).hom
    (pbcDerivedExtend (completedCoefficientMap l E L i X)).map
        (podCompletedToTowerIso l E g K).hom ≫
      (completedScalarComparison l E L i X).app KE.obj ≫ δ.hom =
    (completedScalarReindex l E L i g).hom.app K.obj ≫
      (podCompletedDerivedInverseImage l L g).map
        ((completedScalarComparison l E L i Y).app K.obj) ≫
      (podCompletedToTowerIso l L g KL).hom := by
  simpa only [podCompletedToTowerIso, asIso_hom, constructibleIntegralPullback,
    sfConstructibleIntegralScalarExtension, ObjectProperty.lift, Functor.comp_obj,
    ObjectProperty.ι_obj, pbcDerivedExtend, reductionDerivedChange,
    completedAdicDerivedChange, completedDerivedScalarExtension,
    completedScalarChangeData, completedAdicChangeData] using
    completion_scalar_square l E L i g hX hY K

end WeilConjectures.AdicQbarRealization

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified scalar pullback mate commutes with canonical scalar reassociation.
Source: current blueprint `det-prop-scalar-six-pullback`, proof (1) and (3).
(blueprint: lem-pod-completed-comparison-scalar-square).

Proof: take the already constructed normalized pullback data. Its tower equation
uses the canonical scalar reassociation. Its normalization identifies each of the
three comparison maps with the specified scalar-adjunction mate. Substitute these
three equalities. This proves equality of the actual derived morphisms, without
using finite reductions or any flatness hypothesis. -/
theorem completion_scalar_square
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ g).obj K) ≫
        (scalarSixPullHom (a ≫ b) g).app K =
      (scalarSixChange b X).map ((scalarSixPullHom a g).app K) ≫
        (scalarSixPullHom b g).app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' g).map ((scalarSixTower a b Y).hom.app K) := by
  obtain ⟨C⟩ := scalarSixPullbackData_exists.{u}
  simpa only [C.thetaNormalization] using C.tower a b g K

/-- The same square as an equality of natural transformations on the entire
unbounded derived category, including its constructible objects.
Source: current blueprint `det-prop-scalar-six-pullback`, proof (1) and (3).
(blueprint: lem-pod-completed-comparison-scalar-square).

Proof: evaluate both composites at an arbitrary object. Functor associators have
identity components, and whiskering evaluates to functorial application. The
component equation is exactly completion_scalar_square. -/
theorem completion_constructible_scalar_square
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Functor.whiskerLeft (scalarSixPull Λ g) (scalarSixTower a b X).hom ≫
        scalarSixPullHom (a ≫ b) g =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (scalarSixPullHom a g) (scalarSixChange b X) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (scalarSixChange a Y) (scalarSixPullHom b g) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (scalarSixTower a b Y).hom (scalarSixPull Λ'' g) := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    completion_scalar_square a b g K

end AlgebraicGeometry.ProEtale.CondensedRing
