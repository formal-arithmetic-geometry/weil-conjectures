/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceDiagram
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceHead
import WeilConjectures.SixFunctors.AdicQbarRealization.PodCompletedComparisonScalarSquare
public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex
public import WeilConjectures.SixFunctors.AdicQbarRealization.PodCompletedComparisonNormalization

/-! # The completed source scalar diagram square

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-square)
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

open ScalarSourceCalculus

attribute [local implicit_reducible] StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

-- Keep the selected comparison maps abstract while checking the final square.
attribute [local irreducible] completedScalarReindex completedReindexModel scalarExactModel
  integralPullbackScalarComparison podCompletedToTowerIso pbcReductionNormalization
  pbcReductionNormalizationHom pbcReductionTransition
  podCompletedToTower pbcDerivedScalarAdjunction
attribute [local implicit_reducible] ordinary coefficientMap
  LocallyFiniteAdicRealization.ringSheaf AlgebraicGeometry.Scheme.residueField

set_option maxHeartbeats 1600000 in
-- The square compares several presentations of the derived scalar functors.

/-- Scalar extension commutes with the actual completion-unit pullback comparison.
Source: BS Lemma 6.5.9(4), Proposition 6.8.14 and Remark 6.8.15.
Legacy proof archive; not a declaration of the condensed blueprint route.

Proof: identify each actual comparison with the normalized inverse-image comparison.
Use the existing scalar-extension square for that comparison. The counit-normalized
scalar model identifies its completion map with scalarCompletion. Cancel its
invertible exact-model component on the complete inverse-image object. Naturality
moves these model changes across the comparison, and the inverse coefficient-map
presentation changes cancel. This gives the specified completedScalarReindex map. -/
private theorem completion_scalar_square_legacy (l : ℕ) [Fact l.Prime]
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
        (scalarCompletion l E L i W).app A := by
    simpa only [scalarExactModel, NatTrans.comp_app] using
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
Legacy proof archive; not a declaration of the condensed blueprint route.
Proof: apply completion_scalar_square and expose only the full-subcategory object
maps and the two identical universal derived scalar-extension presentations. -/
private theorem completion_constructible_scalar_square_legacy (l : ℕ) [Fact l.Prime]
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
    completion_scalar_square_legacy l E L i g hX hY K


-- Keep the selected comparison maps abstract while checking the final square.

/-- Paste the head and completion squares in the concrete diagram.
Source: BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-square).
Proof: the head computation supplies the first diagram square. Invertibility of l
in residue fields makes it a unit in all stalks, so the completed comparison square
supplies the second. Apply the generic pasting theorem to these two proved equations. -/
theorem sourceScalarDiagram_square (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let d := sourceScalarDiagram l g R E L h K
    d.f ≫ d.srcL = d.srcE ≫ d.n d.E ≫ d.NL.map d.b ≫ d.NL.map d.c := by
  let C := Coefficient.{u} l (PadicAlgCl l)
  let i := coefficientInclusion l (PadicAlgCl l) E L h
  have hhead := source_scalar_head l g R E L h K
  dsimp only at hhead
  dsimp only [nativeScalarTransition] at hhead
  simp only [Category.assoc] at hhead
  have hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [Scheme.residueField, map_natCast] using
      (isUnit_of_invertible (l : X.residueField x)).ne_zero
  have hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y) := by
    intro y
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [Scheme.residueField, map_natCast] using
      (isUnit_of_invertible (l : Y.residueField y)).ne_zero
  have hsquare := completion_constructible_scalar_square_legacy l (C E) (C L) i g hX hY K
  exact (sourceScalarDiagram l g R E L h K).square
    hhead hsquare

end WeilConjectures.AdicQbarRealization
