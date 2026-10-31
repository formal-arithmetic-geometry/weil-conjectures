/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationChartExistence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationCompatibility
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine refinement of the diagonal orientation

Proof of the four-factor refinement theorem. The canonical maps and predicates are
reexported without change from DiagonalOrientationRefinementData.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace WeilConjectures.PurityFiniteSetting
namespace OrientationRefinement

private theorem four_factor {C : Type*} [Category C]
    {O A B N T O' A' B' N' T' : C}
    (r : O ≅ A) (a : B ≅ A) (c : B ≅ N) (b : N ≅ T)
    (r' : O' ≅ A') (a' : B' ≅ A') (c' : B' ≅ N') (b' : N' ≅ T')
    (s : O ≅ O') (ef : A ≅ A') (ec : B ≅ B') (en : N ≅ N') (t : T ≅ T')
    (hr : r ≪≫ ef = s ≪≫ r') (ha : a ≪≫ ef = ec ≪≫ a')
    (hc : c ≪≫ en = ec ≪≫ c') (hb : b ≪≫ t = en ≪≫ b') :
    s ≪≫ (r' ≪≫ a'.symm ≪≫ c' ≪≫ b') = (r ≪≫ a.symm ≪≫ c ≪≫ b) ≪≫ t := by
  have hai : ef ≪≫ a'.symm = a.symm ≪≫ ec := by
    apply Iso.ext
    apply (cancel_epi a.hom).1
    have hh := congrArg Iso.hom ha
    simp only [Iso.trans_hom, Iso.symm_hom] at hh ⊢
    rw [← Category.assoc, hh, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  calc
    _ = (s ≪≫ r') ≪≫ a'.symm ≪≫ c' ≪≫ b' := by simp only [Iso.trans_assoc]
    _ = r ≪≫ (ef ≪≫ a'.symm) ≪≫ c' ≪≫ b' := by rw [← hr]; simp only [Iso.trans_assoc]
    _ = r ≪≫ a.symm ≪≫ ec ≪≫ c' ≪≫ b' := by rw [hai]; simp only [Iso.trans_assoc]
    _ = r ≪≫ a.symm ≪≫ (c ≪≫ en) ≪≫ b' := by rw [hc]; simp only [Iso.trans_assoc]
    _ = r ≪≫ a.symm ≪≫ c ≪≫ (b ≪≫ t) := by rw [hb]; simp only [Iso.trans_assoc]
    _ = _ := by simp only [Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compatible_agrees (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (D : Chart P f aY d V) (D' : Chart P f aY d V') (h : V'.1 ≤ V.1)
    (hc : Compatible P f aY d D D' h) : Agrees P f aY d D D' h := by
  obtain ⟨sq, G, hρ, hα, hδ, hβ⟩ := hc
  dsimp only [Agrees, theta]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  exact four_factor _ _ _ _ _ _ _ _ _ _ _ _ _ hρ hα hδ hβ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_eq (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) [SmoothOfRelativeDimension d f] {V V' : Y.affineOpens}
    (D : Chart P f aY d V) (D' : Chart P f aY d V') (h : V'.1 ≤ V.1)
    (ha : Agrees P f aY d D D' h) :
    restricted P f aY d D h = theta P f aY d V' D'.geometry D'.betaEtale := by
  dsimp only [restricted]
  dsimp only [Agrees] at ha
  rw [← ha, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

private theorem overlap_cover (P : PurityFiniteSetting.{u}) {Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY]
    (V₁ V₂ : Y.affineOpens) :
    (⨆ W : {W : Y.affineOpens // (W.1.ι ≫ aY).appTop.hom.FiniteType ∧
      W.1 ≤ V₁.1 ⊓ V₂.1}, W.val.1) = V₁.1 ⊓ V₂.1 := by
  apply le_antisymm
  · exact iSup_le fun W ↦ W.2.2
  · intro x hx
    obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens hx
    let W : Y.affineOpens := ⟨U, hU⟩
    let : IsAffine W.1.toScheme := W.2
    have hft : (W.1.ι ≫ aY).appTop.hom.FiniteType :=
      HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp inferInstance
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hft, hUV⟩, hxU⟩

end OrientationRefinement

-- Retain the published restriction statement's redundant finite-type witnesses.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zero-section Tate comparison and compatibility of all four specified local factors
with every affine target refinement. All coefficient levels n >= 1 and all d >= 0
are included, with no absolute separatedness assumption on X or Y.
Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Step 2 and combining paragraph
(blueprint: lem-pur-diagonal-orientation-refinement).

Proof:
1. The chart-existence theorem applies affineTargetDiagonalDnc, identifies the actual
   Rees normal cone with its rank-d conormal vector bundle, and transports the inverse
   integration adjunct through the specified section exchange. Zero-section integration
   base change makes this comparison independent of the vector-bundle presentation.
2. Choose one such normalized chart on every finite-type affine target open.
   The chart-compatibility theorem constructs the Cartesian restriction square and
   the coefficientwise Rees normal map. Exchange pasting proves its rho and alpha
   equations, normalized DNC restriction proves delta, and integration base change
   together with BetaNormalized proves beta.
3. Substitute these four equations in theta. The elementary four-factor cancellation
   identity gives Agrees. Canceling the source comparison identifies every restricted
   orientation with the chosen orientation of the smaller open.
4. Apply that identification twice to prove equality of direct and successive
   restriction. Thus no additional coherence choice is made for chains of opens.
5. The affine opens form a basis on the intersection of two target opens. Local finite
   type of the structural map gives the required appTop finite-type condition on each
   affine subopen. The two restrictions both equal its chosen orientation. The basis
   argument also covers an empty overlap; the preceding arguments include rank zero. -/
theorem diagonalOrientationRefinement (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ D : ∀ (V : Y.affineOpens), (V.1.ι ≫ aY).appTop.hom.FiniteType →
        OrientationRefinement.Chart P f aY d V,
      (∀ (V V' : Y.affineOpens)
        (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
        (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1),
        OrientationRefinement.Compatible P f aY d (D V hV) (D V' hV') h ∧
        OrientationRefinement.Agrees P f aY d (D V hV) (D V' hV') h) ∧
      (∀ (V V' V'' : Y.affineOpens)
        (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
        (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType)
        (hV'' : (V''.1.ι ≫ aY).appTop.hom.FiniteType)
        (h₁ : V'.1 ≤ V.1) (h₂ : V''.1 ≤ V'.1),
        OrientationRefinement.restricted P f aY d (D V hV) (h₂.trans h₁) =
          (OrientationRefinement.sourceComposition P f aY h₂).symm ≪≫
            (OrientationRefinement.pull P (OrientationRefinement.inclusion f h₂)).mapIso
              (OrientationRefinement.restricted P f aY d (D V hV) h₁) ≪≫
            OrientationRefinement.tate P (OrientationRefinement.inclusion f h₂)
              ((f ∣_ V'.1) ≫ V'.1.ι ≫ aY) d) ∧
      (∀ (V₁ V₂ : Y.affineOpens)
        (hV₁ : (V₁.1.ι ≫ aY).appTop.hom.FiniteType)
        (hV₂ : (V₂.1.ι ≫ aY).appTop.hom.FiniteType),
        (⨆ W : {W : Y.affineOpens // (W.1.ι ≫ aY).appTop.hom.FiniteType ∧
          W.1 ≤ V₁.1 ⊓ V₂.1}, W.val.1) = V₁.1 ⊓ V₂.1 ∧
        ∀ (W : Y.affineOpens) (hW : (W.1.ι ≫ aY).appTop.hom.FiniteType)
          (h₁ : W.1 ≤ V₁.1) (h₂ : W.1 ≤ V₂.1),
          OrientationRefinement.restricted P f aY d (D V₁ hV₁) h₁ =
              OrientationRefinement.theta P f aY d W (D W hW).geometry (D W hW).betaEtale ∧
          OrientationRefinement.restricted P f aY d (D V₂ hV₂) h₂ =
              OrientationRefinement.theta P f aY d W (D W hW).geometry (D W hW).betaEtale) := by
  classical
  have hCharts : ∀ (V : Y.affineOpens), (V.1.ι ≫ aY).appTop.hom.FiniteType →
      Nonempty (OrientationRefinement.Chart P f aY d V) := by
    intro V hV
    exact OrientationRefinement.diagonalOrientationChart_exists P aY aX f hf d V hV
  let D := fun V hV ↦ Classical.choice (hCharts V hV)
  have hFactors : ∀ (V V' : Y.affineOpens)
      (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1),
      OrientationRefinement.Compatible P f aY d (D V hV) (D V' hV') h := by
    intro V V' hV hV' h
    exact OrientationRefinement.diagonalOrientationCompatible P aY aX f hf d
      V V' hV hV' h (D V hV) (D V' hV')
  have ha (V V' : Y.affineOpens)
      (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1) :=
    OrientationRefinement.compatible_agrees P f aY d (D V hV) (D V' hV') h
      (hFactors V V' hV hV' h)
  have hr (V V' : Y.affineOpens)
      (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1) :=
    OrientationRefinement.restricted_eq P f aY d (D V hV) (D V' hV') h
      (ha V V' hV hV' h)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro V V' hV hV' h
    exact ⟨hFactors V V' hV hV' h, ha V V' hV hV' h⟩
  · intro V V' V'' hV hV' hV'' h₁ h₂
    rw [hr V V'' hV hV'' (h₂.trans h₁), hr V V' hV hV' h₁]
    exact (hr V' V'' hV' hV'' h₂).symm
  · intro V₁ V₂ hV₁ hV₂
    refine ⟨OrientationRefinement.overlap_cover P aY V₁ V₂, ?_⟩
    intro W hW h₁ h₂
    exact ⟨hr V₁ W hV₁ hW h₁, hr V₂ W hV₂ hW h₂⟩

end WeilConjectures.PurityFiniteSetting
