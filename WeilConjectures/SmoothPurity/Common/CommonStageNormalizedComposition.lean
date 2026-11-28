/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackCoefficientUnit
import all Mathlib.Logic.Small.Defs

/-! # Generic normalized composition cancellation

A coherence lemma for normalized compositors: three unit comparisons compatible with given
isomorphisms `S ≅ 𝟭`, `T ≅ 𝟭`, `U ≅ 𝟭` cancel against a composition isomorphism
`H ≅ G ⋙ F`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

-- Use the same cached category structures as the coefficient comparison APIs.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
  GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

/-- Three compatible unit comparisons cancel in a normalized compositor: if
`aH`, `aG`, `aF` are compatible with the unit isomorphisms `s`, `t`, `u`, then
`aH ≫ α_{S K} ≫ F(aG⁻¹) ≫ aF⁻¹ = U(α_K)`. -/
theorem commonStageNormalizedComposition
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (G : C ⥤ D) (F : D ⥤ B) (H : C ⥤ B)
    (S : C ⥤ C) (T : D ⥤ D) (U : B ⥤ B)
    (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D) (u : U ≅ 𝟭 B)
    (α : H ≅ G ⋙ F) (K : C)
    (aH : U.obj (H.obj K) ≅ H.obj (S.obj K))
    (aG : T.obj (G.obj K) ≅ G.obj (S.obj K))
    (aF : U.obj (F.obj (G.obj K)) ≅ F.obj (T.obj (G.obj K)))
    (hH : aH ≪≫ H.mapIso (s.app K) = u.app (H.obj K))
    (hG : aG ≪≫ G.mapIso (s.app K) = t.app (G.obj K))
    (hF : aF ≪≫ F.mapIso (t.app (G.obj K)) = u.app (F.obj (G.obj K))) :
    aH.hom ≫ α.hom.app (S.obj K) ≫ F.map aG.inv ≫ aF.inv =
      U.map (α.hom.app K) := by
  have eH : aH.hom = (u.app (H.obj K)).hom ≫ H.map (s.app K).inv := by
    rw [← hH]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_map, Category.comp_id]
  have eG : aG.inv = G.map (s.app K).hom ≫ (t.app (G.obj K)).inv := by
    rw [← hG]
    dsimp only [Iso.trans_inv, Functor.mapIso_inv]
    rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  have eF : aF.inv = F.map (t.app (G.obj K)).hom ≫
      (u.app (F.obj (G.obj K))).inv := by
    rw [← hF]
    dsimp only [Iso.trans_inv, Functor.mapIso_inv]
    rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  dsimp only [Functor.id_obj] at *
  rw [eH, eG, eF]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc]
  have hn := α.hom.naturality (s.app K).inv
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc (H.map _), hn]
  simp only [Category.assoc, ← F.map_comp_assoc, ← G.map_comp,
    Iso.inv_hom_id]
  simpa using (NatIso.naturality_2 u (α.hom.app K))

end WeilConjectures
