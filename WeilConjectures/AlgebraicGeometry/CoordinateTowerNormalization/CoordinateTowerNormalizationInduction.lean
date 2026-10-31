/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationData

import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerExceptionalCompositors
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationFusion
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerCompactTranspose

/-! # Coordinate-tower normalization induction

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
open AffineZeroPurity AffineSpacePurity VectorIntegrationSite
attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction identityUnit

private theorem gamma_isIso
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (hl : LineLaw P n B aB c) (r : ℕ) (hr : r ≤ c) :
    IsIso (gamma P n B aB r) := by
  induction r with
  | zero =>
    unfold gamma affineSpacePurityComparison orderedRec comparisonZero
    delta orderedSource exceptional
    dsimp only [id]
    exact @CategoryTheory.IsIso.id
      (AffineSpacePurity.D (setting P n) (iteratedAffineLine B 0)) inferInstance _
  | succ r ih =>
    have hprev := ih (Nat.le_of_succ_le hr)
    have hcomp := (exceptionalCompositors_isIso P n B aB r).1
    let K : Plus (setting P n).Coefficient B := ⟨_, (unit_origin P n B).plus⟩
    let Ke := (_root_.DerivedCategory.singleFunctor _ 0).obj ((setting P n).constantEtale B)
    let hKe := unit_finiteTor P n B
    let eK := (Functor.mapDerivedCategorySingleFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} (setting P n).Coefficient) B) 0).app
        ((setting P n).constantEtale B) ≪≫ (eqToIso (unit_single_eq P n B)).symm
    have hstage := stage_applicability (setting P n) B aB K Ke hKe eK r
    unfold LineLaw at hl
    have hline := hl ⟨r, Nat.lt_of_succ_le hr⟩
    have hi := hline.1
      ⟨(exceptional (setting P n) B r).obj K.obj, hstage.1⟩
      (stageEtale (setting P n) B K.obj Ke r)
      hstage.2
      (stageComparison (setting P n) B K.obj Ke eK r)
    unfold lineGamma at hi
    unfold gamma affineSpacePurityComparison
    rw [orderedRec]
    dsimp only [comparisonStep]
    unfold gamma affineSpacePurityComparison at hprev
    let hprevIso : IsIso (orderedRec (comparisonZero (setting P n) B (unit P n B))
        (comparisonStep (setting P n) B aB K Ke hKe eK) r) := hprev
    have hm : IsIso ((lineSource (setting P n) (iteratedAffineLine B r)).map
        (orderedRec (comparisonZero (setting P n) B (unit P n B))
          (comparisonStep (setting P n) B aB K Ke hKe eK) r)) := by
      infer_instance
    exact CategoryTheory.IsIso.comp_isIso'
      (sourceReassociation (setting P n) B aB (unit P n B) r).isIso_hom
      (CategoryTheory.IsIso.comp_isIso' hm
        (CategoryTheory.IsIso.comp_isIso' hi hcomp))

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
