/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingFirstFactor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingSecondFactor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingSigmaBaseChange

/-! # Base change of the ordinary standard section-pasting map

Source: composition coherence Step 1, compatible-DNC-charts proof Step 8.
(blueprint: lem-route-standard-section-pasting-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

-- These proved tensor lemmas are kept local: the interface snapshot does not
-- expose the private helpers of PurityDiagonalGlobalEquation.
private def pastingBimapIso {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {K K' : C} {M M' : D} (a : K ≅ K') (b : M ≅ M') :
    (F.obj K).obj M ≅ (F.obj K').obj M' :=
  (F.mapIso a).app M ≪≫ (F.obj K').mapIso b

private theorem pastingBimapIso_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {K K' K'' : C} {M M' M'' : D}
    (a : K ≅ K') (b : M ≅ M') (c : K' ≅ K'') (d : M' ≅ M'') :
    pastingBimapIso F a b ≪≫ pastingBimapIso F c d = pastingBimapIso F (a ≪≫ c) (b ≪≫ d) := by
  apply Iso.ext
  dsimp only [pastingBimapIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% (F.map c.hom).naturality b.hom]

private theorem pastingPullbackTensor (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [(Etale.upperStar B f).PreservesFlat]
    {K K' M M' : DerivedCategory (Sheaf Y.smallEtaleTopology B)}
    (a : K ≅ K') (b : M ≅ M') :
    (Etale.upperStar B f).leftDerivedFunctor.mapIso
        (pastingBimapIso (Etale.derivedTensor B Y) a b) ≪≫
      Etale.leftDerivedUpperStarTensorIso B f K' M' =
    Etale.leftDerivedUpperStarTensorIso B f K M ≪≫
      pastingBimapIso (Etale.derivedTensor B X)
        ((Etale.upperStar B f).leftDerivedFunctor.mapIso a)
        ((Etale.upperStar B f).leftDerivedFunctor.mapIso b) := by
  apply Iso.ext
  dsimp only [pastingBimapIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [Etale.leftDerivedUpperStarTensorIso_hom_naturality_right,
    Etale.leftDerivedUpperStarTensorIso_hom_naturality_left_assoc]


private theorem pastingBaseChange_eq (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (r : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :
    letI := Dnc.invertibleExponent P (DiagonalPasting.pr r B ≫ aB)
    letI := DiagonalPasting.affineDimension r B
    Dnc.sectionBaseChange P.Coefficient r (DiagonalPasting.pr r B)
      (AffineSpace.isPullback_map b) (DiagonalPasting.zero r B)
      (DiagonalPasting.zero r B') (AffineSpace.zeroSection_comp_map b) =
      StandardPasting.baseChange P r b aB := by
  let := Dnc.invertibleExponent P (DiagonalPasting.pr r B ≫ aB)
  let := DiagonalPasting.affineDimension r B
  delta Dnc.sectionBaseChange StandardPasting.baseChange
  delta Etale.sectionCoherencePullbackIso DiagonalPasting.beta Etale.sectionInvariant
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, asIso_hom, Category.assoc]

set_option maxHeartbeats 1500000 in
-- Derived pullback coherence comparisons have large elaborated types.
/-- The ordinary etale geometric part of standard section-pasting base change.
No comparison between sites or pro-etale tensor constraint enters this equation.
Source: composition coherence Step 1; compatible-DNC-charts proof Step 8
(blueprint: lem-route-standard-section-pasting-base-change).

Proof: write nu as the zero-section pullback of sigma for the ordered tower
A^(d+e)_B -> A^e_B -> B, preceded by the inverse smooth base-change map for
its first block and the pullback-composition map for its second block. Base
change the tower along b, using the affine-space Cartesian squares. Their
zero sections commute with the affine-space maps, as do both block projections.
The sigma base-change identity of dualizing_sigma_cocycle_locality identifies
pullback of sigma followed by the total dualizing base-change mate with the
tensor of the two factor mates followed by the base-changed sigma. Pull that
identity along the new total zero section. Naturality and composition of the
derived pullback tensor constraint move it before the two factor comparisons.
Pasting Cartesian base-change mates identifies the first factor with the
sectionBaseChange for rank d; coherence of pullback composition identifies the
second with sectionBaseChange for rank e. The total mate is sectionBaseChange
for rank d+e. These substitutions yield the displayed equation, with no
orientation used. All squares and mates exist for empty schemes and empty
coordinate blocks, so the argument includes rank zero. -/
theorem standardSectionPasting_baseChange (P : PurityFiniteSetting.{u})
    {B' B : Scheme.{u}} [IsAffine B'] [IsAffine B]
    (d e : ℕ) (b : B' ⟶ B) [Etale b]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType b] [QuasiCompact b] :
    letI := P.noetherian aB
    letI := P.noetherian (b ≫ aB)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let bc := fun r : ℕ ↦
      letI := Dnc.invertibleExponent P (DiagonalPasting.pr r B ≫ aB)
      letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
      letI := Dnc.compactifiable P (DiagonalPasting.pr r B') (b ≫ aB)
      letI := DiagonalPasting.affineDimension r B
      Dnc.sectionBaseChange P.Coefficient r (DiagonalPasting.pr r B)
        (AffineSpace.isPullback_map b) (DiagonalPasting.zero r B)
        (DiagonalPasting.zero r B') (AffineSpace.zeroSection_comp_map b)
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (DiagonalPasting.nu P.Coefficient P d e B aB) ≪≫ bc (d + e) =
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) b
        (DiagonalPasting.zeroInvariant P.Coefficient P d B)
        (DiagonalPasting.zeroInvariant P.Coefficient P e B) ≪≫
      DiagonalPasting.tensorComparison P.Coefficient P (bc d) (bc e) ≪≫
        DiagonalPasting.nu P.Coefficient P d e B' (b ≫ aB) := by
  let := P.noetherian aB
  let := P.noetherian (b ≫ aB)
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  dsimp only
  let F := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
  let c₁ := StandardPasting.firstInput P d e B aB
  let c₂ := StandardPasting.secondInput P d e B
  let k₁ := StandardPasting.firstChange P d e b aB
  let k₂ := StandardPasting.secondChange P d e b aB
  let bc := fun r ↦ StandardPasting.baseChange P r b aB
  let T := fun {X : Scheme.{u}} {K K' M M' : Etale.DerivedCategoryModule P.Coefficient X}
      (a : K ≅ K') (b : M ≅ M') ↦
    DiagonalPasting.tensorComparison P.Coefficient P a b
  have h₁ := StandardPasting.first_factor_identity P d e b aB
  have h₂ := StandardPasting.second_factor_identity P d e b aB
  have hσ := StandardPasting.sigma_baseChange_pulled P d e b aB
  have hn := pastingPullbackTensor
    (ModuleCat.{u + 1} P.Coefficient) b c₁ c₂
  change F.mapIso (T c₁ c₂) ≪≫ _ = _ ≪≫ T (F.mapIso c₁) (F.mapIso c₂) at hn
  have hc := pastingBimapIso_comp
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B')
    (F.mapIso c₁) (F.mapIso c₂) k₁ k₂
  change T (F.mapIso c₁) (F.mapIso c₂) ≪≫ T k₁ k₂ =
    T (F.mapIso c₁ ≪≫ k₁) (F.mapIso c₂ ≪≫ k₂) at hc
  have hc' := pastingBimapIso_comp
    (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B')
    (bc d) (bc e) (StandardPasting.firstInput P d e B' (b ≫ aB))
    (StandardPasting.secondInput P d e B')
  change T (bc d) (bc e) ≪≫
      T (StandardPasting.firstInput P d e B' (b ≫ aB))
        (StandardPasting.secondInput P d e B') =
    T (bc d ≪≫ StandardPasting.firstInput P d e B' (b ≫ aB))
      (bc e ≪≫ StandardPasting.secondInput P d e B') at hc'
  have h : F.mapIso (DiagonalPasting.nu P.Coefficient P d e B aB) ≪≫ bc (d+e) =
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) b
        (DiagonalPasting.zeroInvariant P.Coefficient P d B)
        (DiagonalPasting.zeroInvariant P.Coefficient P e B) ≪≫
      T (bc d) (bc e) ≪≫ DiagonalPasting.nu P.Coefficient P d e B' (b ≫ aB) := by
    rw [StandardPasting.nu_eq, StandardPasting.nu_eq]
    erw [Functor.mapIso_trans]
    erw [Iso.trans_assoc]
    erw [hσ, ← Iso.trans_assoc (F.mapIso (T c₁ c₂)), hn]
    erw [Iso.trans_assoc]
    erw [← Iso.trans_assoc (T (F.mapIso c₁) (F.mapIso c₂)), hc, h₁, h₂,
      ← hc']
    erw [Iso.trans_assoc]
    delta DiagonalPasting.zeroInvariant
    delta Etale.sectionInvariant
    rfl
  erw [pastingBaseChange_eq P (d+e) b aB, pastingBaseChange_eq P d b aB,
    pastingBaseChange_eq P e b aB]
  exact h

end WeilConjectures.PurityFiniteSetting
