/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOpenBaseChangeEvaluation
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowEvaluation
import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization

/-! # Evaluation compatibility of the intrinsic inverse-image clopen word

Source: Stacks Project, Tag 0F7B, open case; Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
open Normalization
namespace GenericComposition
private def composeComparison
    {A B D A' B' D' : Type*}
    [Category A] [Category B] [Category D]
    [Category A'] [Category B'] [Category D']
    {F : A ⥤ B} {G : B ⥤ D} {F' : A' ⥤ B'} {G' : B' ⥤ D'}
    {U : A ⥤ A'} {V : B ⥤ B'} {W : D ⥤ D'}
    (f : F ⋙ V ≅ U ⋙ F') (g : G ⋙ W ≅ V ⋙ G') :
    (F ⋙ G) ⋙ W ≅ U ⋙ (F' ⋙ G') :=
  Functor.associator F G W ≪≫ Functor.isoWhiskerLeft F g ≪≫
    (Functor.associator F V G').symm ≪≫ Functor.isoWhiskerRight f G' ≪≫
    Functor.associator U F' G'

private theorem composeComparison_app
    {A B D A' B' D' : Type*}
    [Category A] [Category B] [Category D]
    [Category A'] [Category B'] [Category D']
    {F : A ⥤ B} {G : B ⥤ D} {F' : A' ⥤ B'} {G' : B' ⥤ D'}
    {U : A ⥤ A'} {V : B ⥤ B'} {W : D ⥤ D'}
    (f : F ⋙ V ≅ U ⋙ F') (g : G ⋙ W ≅ V ⋙ G') (M : A) :
    (composeComparison f g).hom.app M = g.hom.app (F.obj M) ≫
      G'.map (f.hom.app M) := by
  change 𝟙 _ ≫ g.hom.app (F.obj M) ≫ 𝟙 _ ≫
    G'.map (f.hom.app M) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

end GenericComposition
open GenericComposition

section ExactEvaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  (F₀₁ : A₀ ⥤ A₁) (F₁₂ : A₁ ⥤ A₂) (F₀₂ : A₀ ⥤ A₂)
  (G₀₁ : B₀ ⥤ B₁) (G₁₂ : B₁ ⥤ B₂) (G₀₂ : B₀ ⥤ B₂)
  (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]

private theorem exact_evaluation_pasting
    (s : U₀ ⋙ G₀₁ ≅ F₀₁ ⋙ U₁) (q : U₁ ⋙ G₁₂ ≅ F₁₂ ⋙ U₂)
    (g : U₀ ⋙ G₀₂ ≅ F₀₂ ⋙ U₂)
    (a : G₀₁ ⋙ G₁₂ ≅ G₀₂) (b : F₀₁ ⋙ F₁₂ ≅ F₀₂)
    (h : ∀ N, g.hom.app N ≫ U₂.map (b.inv.app N) =
      a.inv.app (U₀.obj N) ≫ G₁₂.map (s.hom.app N) ≫ q.hom.app (F₀₁.obj N))
    (M : DerivedCategory A₀) :
    G₁₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso s).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso q).hom.app (F₀₁.mapDerivedCategory.obj M) ≫
        U₂.mapDerivedCategory.map
          (((Functor.mapDerivedCategoryCompIso F₀₁ F₁₂).symm ≪≫
            Functor.mapDerivedCategoryNatIso b).hom.app M) =
      ((Functor.mapDerivedCategoryCompIso G₀₁ G₁₂).symm ≪≫
          Functor.mapDerivedCategoryNatIso a).hom.app (U₀.mapDerivedCategory.obj M) ≫
        (Functor.mapDerivedCategorySquareIso g).hom.app M := by
  have hh := Functor.exactSquare_comp_inverse
    F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂ s q g b.symm a.symm h M
  apply (cancel_epi
    ((Functor.mapDerivedCategoryNatIso a.symm ≪≫
      Functor.mapDerivedCategoryCompIso G₀₁ G₁₂).hom.app
        (U₀.mapDerivedCategory.obj M))).mp
  apply (cancel_mono
    (U₂.mapDerivedCategory.map
      ((Functor.mapDerivedCategoryNatIso b.symm ≪≫
        Functor.mapDerivedCategoryCompIso F₀₁ F₁₂).hom.app M))).mp
  have hh' := hh.symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at hh' ⊢
  erw [U₂.mapDerivedCategory.map_id, Category.comp_id]
  exact hh'
end ExactEvaluation

section ConstantEvaluation
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso
variable {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
  [Abelian A] [Abelian B] [Abelian D] [Abelian F]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory F]
  [HasDerivedCategory (ℕᵒᵖ ⥤ D)] [HasDerivedCategory (ℕᵒᵖ ⥤ F)]
  (L : A ⥤ B) (G : B ⥤ D) (H : A ⥤ F) (I : F ⥤ D)
  [L.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ F D).obj I)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ F D).obj I)]

private def constantEvaluationBridge {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (F ⋙ Functor.const ℕᵒᵖ).mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj (op 0)).mapDerivedCategory ≅
      F.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (F ⋙ Functor.const ℕᵒᵖ)
    ((CategoryTheory.evaluation ℕᵒᵖ B).obj (op 0))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl F)

private theorem constant_evaluation (e : L ⋙ G ≅ H ⋙ I) (M : DerivedCategory A) :
    (((CategoryTheory.evaluation ℕᵒᵖ D).obj (op 0)).mapDerivedCategory).map
        ((Functor.mapDerivedCategorySquareIso
          (SemilinearProperOpenCoreAliases.constant_diagram_square L G H I e)).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (F₁ := (Functor.whiskeringRight ℕᵒᵖ F D).obj I)
        (F₂ := (CategoryTheory.evaluation ℕᵒᵖ D).obj (op 0))
        (G₁ := (CategoryTheory.evaluation ℕᵒᵖ F).obj (op 0))
        (G₂ := I) (Iso.refl _)).hom.app
          ((H ⋙ Functor.const ℕᵒᵖ).mapDerivedCategory.obj M) ≫
      I.mapDerivedCategory.map ((constantEvaluationBridge H).hom.app M) =
    (constantEvaluationBridge G).hom.app (L.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app M := by
  exact exact_evaluation_pasting
    (H ⋙ Functor.const ℕᵒᵖ)
    ((CategoryTheory.evaluation ℕᵒᵖ F).obj (op 0)) H
    (G ⋙ Functor.const ℕᵒᵖ)
    ((CategoryTheory.evaluation ℕᵒᵖ D).obj (op 0)) G
    L ((Functor.whiskeringRight ℕᵒᵖ F D).obj I) I
    (SemilinearProperOpenCoreAliases.constant_diagram_square L G H I e)
    (Iso.refl _) e (Iso.refl _) (Iso.refl _) (fun N ↦ by
      change e.hom.app N ≫ I.map (𝟙 _) = 𝟙 _ ≫ e.hom.app N ≫ 𝟙 _
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      erw [Category.comp_id]) M
end ConstantEvaluation

private theorem inverse_mate_pasted
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (w₁ : TwoSquare R₁ B₁ T₁ R₂) (w₂ : TwoSquare R₂ B₂ T₂ R₃)
    (w : TwoSquare R₁ S T R₃) (a : T ≅ T₁ ⋙ T₂) (b : S ≅ B₁ ⋙ B₂)
    (h : ∀ X, w.app X ≫ R₃.map (b.hom.app X) =
      a.hom.app (R₁.obj X) ≫ (w₁.vComp w₂).app X) (M : A) :
    ((mateEquiv a₁ a₃).symm w).app M ≫ b.hom.app (L₁.obj M) =
      L₃.map (a.hom.app M) ≫
        ((mateEquiv a₂ a₃).symm w₂).app (T₁.obj M) ≫
        B₂.map (((mateEquiv a₁ a₂).symm w₁).app M) := by
  let v := ((mateEquiv a₁ a₂).symm w₁).hComp ((mateEquiv a₂ a₃).symm w₂)
  have hv : mateEquiv a₁ a₃ v = w₁.vComp w₂ := by
    dsimp only [v]
    rw [mateEquiv_vcomp a₁ a₂ a₃, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hw : mateEquiv a₁ a₃ ((v.whiskerTop a.hom).whiskerBottom b.inv) = w := by
    rw [mateEquiv_whiskerTop_whiskerBottom, hv]
    ext X
    apply (cancel_mono (R₃.map (b.hom.app X))).mp
    simpa [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, Category.assoc,
      ← R₃.map_comp] using (h X).symm
  rw [← hw, Equiv.symm_apply_apply]
  dsimp only [v, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.assoc, Category.id_comp, Category.comp_id, b.inv_hom_id_app]
  erw [Category.comp_id]

private theorem inverse_mate_of_mate
    {A B D F : Type*} [Category A] [Category B] [Category D] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {T : A ⥤ D} {S : B ⥤ F}
    (v : T ⋙ L₂ ⟶ L₁ ⋙ S) (w : R₁ ⋙ T ⟶ S ⋙ R₂)
    (h : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ v)).natTrans = w) :
    ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ w)).natTrans = v := by
  have he : mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ v) = TwoSquare.mk _ _ _ _ w := by
    ext N
    exact NatTrans.congr_app h N
  have hh := congrArg (fun t ↦ ((mateEquiv a₁ a₂).symm t).natTrans) he
  simpa only [Equiv.symm_apply_apply] using hh.symm

private theorem inverse_mate_evaluation
    {A B D F H I : Type*} [Category A] [Category B] [Category D]
    [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    {L₃ : H ⥤ I} {R₃ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {T₁ : A ⥤ D} {B₁ : B ⥤ F} {T₂ : D ⥤ H} {B₂ : F ⥤ I}
    {T : A ⥤ H} {S : B ⥤ I}
    (s : R₁ ⋙ T₁ ≅ B₁ ⋙ R₂) (q : R₂ ⋙ T₂ ≅ B₂ ⋙ R₃)
    (g : R₁ ⋙ T ≅ S ⋙ R₃)
    (j : L₁ ⋙ B₁ ≅ T₁ ⋙ L₂) (k : L₂ ⋙ B₂ ≅ T₂ ⋙ L₃)
    (l : L₁ ⋙ S ≅ T ⋙ L₃)
    (hj : ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ s.hom)).natTrans = j.inv)
    (hk : ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ q.hom)).natTrans = k.inv)
    (hl : ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ g.hom)).natTrans = l.inv)
    (a : T₁ ⋙ T₂ ≅ T) (b : B₁ ⋙ B₂ ≅ S)
    (h : ∀ N, T₂.map (s.hom.app N) ≫ q.hom.app (B₁.obj N) ≫
      R₃.map (b.hom.app N) = a.hom.app (R₁.obj N) ≫ g.hom.app N) (M : A) :
    B₂.map (j.hom.app M) ≫ k.hom.app (T₁.obj M) ≫ L₃.map (a.hom.app M) =
      b.hom.app (L₁.obj M) ≫ l.hom.app M := by
  have hm := inverse_mate_pasted a₁ a₂ a₃
    (TwoSquare.mk _ _ _ _ s.hom) (TwoSquare.mk _ _ _ _ q.hom)
    (TwoSquare.mk _ _ _ _ g.hom) a.symm b.symm (fun N ↦ by
      dsimp only [TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Category.id_comp, Category.comp_id]
      apply (cancel_mono (R₃.map (b.hom.app N))).mp
      simp only [Iso.symm_hom, Category.assoc, ← R₃.map_comp,
        Iso.inv_hom_id_app, R₃.map_id]
      erw [Category.comp_id]
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
        congrArg (fun t ↦ a.inv.app (R₁.obj N) ≫ t) (h N).symm) M
  have hi : l.symm.app M ≪≫ b.symm.app (L₁.obj M) =
      L₃.mapIso (a.symm.app M) ≪≫ k.symm.app (T₁.obj M) ≪≫
        B₂.mapIso (j.symm.app M) := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, hj, hk, hl, Category.assoc] using hm
  simpa only [Iso.trans_inv, Iso.symm_inv, Iso.app, Iso.symm,
    Functor.mapIso_inv, Category.assoc] using (congrArg Iso.inv hi).symm

private theorem map_injective_on_full_image
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) [F.Full] (G : B ⥤ A) (e : F ⋙ G ≅ 𝟭 A)
    {X Y : A} {f g : F.obj X ⟶ F.obj Y} (h : G.map f = G.map g) : f = g := by
  have : (F ⋙ G).Faithful := Functor.Faithful.of_iso e.symm
  have hh : (F ⋙ G).map (F.preimage f) = (F ⋙ G).map (F.preimage g) := by
    simpa only [Functor.comp_map, Functor.map_preimage] using h
  have hh' : F.preimage f = F.preimage g := (F ⋙ G).map_injective hh
  calc
    f = F.map (F.preimage f) := (F.map_preimage f).symm
    _ = F.map (F.preimage g) := congrArg F.map hh'
    _ = g := F.map_preimage g

private theorem comparison_path
    {A B D A' B' D' A'' B'' D'' : Type*}
    [Category A] [Category B] [Category D]
    [Category A'] [Category B'] [Category D']
    [Category A''] [Category B''] [Category D'']
    {F : A ⥤ B} {G : B ⥤ D} {F' : A' ⥤ B'} {G' : B' ⥤ D'}
    {F'' : A'' ⥤ B''} {G'' : B'' ⥤ D''}
    {U₀ : A ⥤ A'} {U₁ : B ⥤ B'} {U₂ : D ⥤ D'}
    {V₀ : A' ⥤ A''} {V₁ : B' ⥤ B''} {V₂ : D' ⥤ D''}
    {W₀ : A ⥤ A''} {W₁ : B ⥤ B''} {W₂ : D ⥤ D''}
    (eF : F ⋙ U₁ ≅ U₀ ⋙ F') (eG : G ⋙ U₂ ≅ U₁ ⋙ G')
    (dF : F' ⋙ V₁ ≅ V₀ ⋙ F'') (dG : G' ⋙ V₂ ≅ V₁ ⋙ G'')
    (qF : F ⋙ W₁ ≅ W₀ ⋙ F'') (qG : G ⋙ W₂ ≅ W₁ ⋙ G'')
    (b₀ : U₀ ⋙ V₀ ≅ W₀) (b₁ : U₁ ⋙ V₁ ≅ W₁) (b₂ : U₂ ⋙ V₂ ≅ W₂)
    (hF : ∀ M, V₁.map (eF.hom.app M) ≫ dF.hom.app (U₀.obj M) ≫
      F''.map (b₀.hom.app M) = b₁.hom.app (F.obj M) ≫ qF.hom.app M)
    (hG : ∀ N, V₂.map (eG.hom.app N) ≫ dG.hom.app (U₁.obj N) ≫
      G''.map (b₁.hom.app N) = b₂.hom.app (G.obj N) ≫ qG.hom.app N)
    (M : A) :
    V₂.map ((composeComparison eF eG).hom.app M) ≫
        (composeComparison dF dG).hom.app (U₀.obj M) ≫
        (F'' ⋙ G'').map (b₀.hom.app M) =
      b₂.hom.app ((F ⋙ G).obj M) ≫ (composeComparison qF qG).hom.app M := by
  simp only [composeComparison_app, Functor.map_comp, Functor.comp_map, Category.assoc]
  have hn := dG.hom.naturality (eF.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  change V₂.map (eG.hom.app (F.obj M)) ≫ dG.hom.app (U₁.obj (F.obj M)) ≫
      G''.map (V₁.map (eF.hom.app M)) ≫ G''.map (dF.hom.app (U₀.obj M)) ≫
      G''.map (F''.map (b₀.hom.app M)) = _
  rw [← G''.map_comp, ← G''.map_comp, hF, G''.map_comp]
  simpa only [Category.assoc, Functor.comp_obj] using
    congrArg (fun t ↦ t ≫ G''.map (qF.hom.app M))
    (hG (F.obj M))

private theorem evaluated_cube
    {A B A' B' A'' B'' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    [Category A''] [Category B'']
    {L R : A ⥤ B} {L' R' : A' ⥤ B'} {L'' R'' : A'' ⥤ B''}
    {U₀ : A ⥤ A'} {U₁ : B ⥤ B'} {V₀ : A' ⥤ A''} {V₁ : B' ⥤ B''}
    {W₀ : A ⥤ A''} {W₁ : B ⥤ B''}
    (a : L ⟶ R) (a' : L' ⟶ R') (a'' : L'' ⟶ R'')
    (eL : L ⋙ U₁ ≅ U₀ ⋙ L') (eR : R ⋙ U₁ ≅ U₀ ⋙ R')
    (dL : L' ⋙ V₁ ≅ V₀ ⋙ L'') (dR : R' ⋙ V₁ ≅ V₀ ⋙ R'')
    (qL : L ⋙ W₁ ≅ W₀ ⋙ L'') (qR : R ⋙ W₁ ≅ W₀ ⋙ R'')
    (b₀ : U₀ ⋙ V₀ ≅ W₀) (b₁ : U₁ ⋙ V₁ ≅ W₁)
    (hL : ∀ M, V₁.map (eL.hom.app M) ≫ dL.hom.app (U₀.obj M) ≫
      L''.map (b₀.hom.app M) = b₁.hom.app (L.obj M) ≫ qL.hom.app M)
    (hR : ∀ M, V₁.map (eR.hom.app M) ≫ dR.hom.app (U₀.obj M) ≫
      R''.map (b₀.hom.app M) = b₁.hom.app (R.obj M) ≫ qR.hom.app M)
    (hq : ∀ M, W₁.map (a.app M) ≫ qR.hom.app M =
      qL.hom.app M ≫ a''.app (W₀.obj M))
    (hd : ∀ N, V₁.map (a'.app N) ≫ dR.hom.app N =
      dL.hom.app N ≫ a''.app (V₀.obj N)) (M : A) :
    V₁.map (U₁.map (a.app M) ≫ eR.hom.app M) =
      V₁.map (eL.hom.app M ≫ a'.app (U₀.obj M)) := by
  apply (cancel_mono (dR.hom.app (U₀.obj M) ≫ R''.map (b₀.hom.app M))).mp
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = V₁.map (U₁.map (a.app M)) ≫
        b₁.hom.app (R.obj M) ≫ qR.hom.app M := by rw [hR]
    _ = b₁.hom.app (L.obj M) ≫ W₁.map (a.app M) ≫ qR.hom.app M := by
      have hn := b₁.hom.naturality (a.app M)
      dsimp only [Functor.comp_map] at hn
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ qR.hom.app M) hn
    _ = b₁.hom.app (L.obj M) ≫ qL.hom.app M ≫ a''.app (W₀.obj M) := by rw [hq]
    _ = (V₁.map (eL.hom.app M) ≫ dL.hom.app (U₀.obj M) ≫
        L''.map (b₀.hom.app M)) ≫ a''.app (W₀.obj M) := by
      rw [hL M, Category.assoc]
    _ = V₁.map (eL.hom.app M) ≫
        (dL.hom.app (U₀.obj M) ≫ a''.app (V₀.obj (U₀.obj M))) ≫
        R''.map (b₀.hom.app M) := by
      rw [Category.assoc, Category.assoc, a''.naturality]
      simp only [Category.assoc]
    _ = _ := by rw [← hd]; simp only [Category.assoc]

private theorem expanded_evaluated_cube
    {A B C D A' B' C' D' A'' B'' C'' D'' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Category A''] [Category B''] [Category C''] [Category D'']
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    {F' : A' ⥤ B'} {G' : B' ⥤ D'} {H' : A' ⥤ C'} {I' : C' ⥤ D'}
    {F'' : A'' ⥤ B''} {G'' : B'' ⥤ D''} {H'' : A'' ⥤ C''} {I'' : C'' ⥤ D''}
    {U₀ : A ⥤ A'} {U₁ : B ⥤ B'} {U₂ : C ⥤ C'} {U₃ : D ⥤ D'}
    {V₀ : A' ⥤ A''} {V₁ : B' ⥤ B''} {V₂ : C' ⥤ C''} {V₃ : D' ⥤ D''}
    {W₀ : A ⥤ A''} {W₁ : B ⥤ B''} {W₂ : C ⥤ C''} {W₃ : D ⥤ D''}
    (a : F ⋙ G ⟶ H ⋙ I) (a' : F' ⋙ G' ⟶ H' ⋙ I') (a'' : F'' ⋙ G'' ⟶ H'' ⋙ I'')
    (eF : F ⋙ U₁ ≅ U₀ ⋙ F') (eG : G ⋙ U₃ ≅ U₁ ⋙ G')
    (eH : H ⋙ U₂ ≅ U₀ ⋙ H') (eI : I ⋙ U₃ ≅ U₂ ⋙ I')
    (dF : F' ⋙ V₁ ≅ V₀ ⋙ F'') (dG : G' ⋙ V₃ ≅ V₁ ⋙ G'')
    (dH : H' ⋙ V₂ ≅ V₀ ⋙ H'') (dI : I' ⋙ V₃ ≅ V₂ ⋙ I'')
    (qF : F ⋙ W₁ ≅ W₀ ⋙ F'') (qG : G ⋙ W₃ ≅ W₁ ⋙ G'')
    (qH : H ⋙ W₂ ≅ W₀ ⋙ H'') (qI : I ⋙ W₃ ≅ W₂ ⋙ I'')
    (b₀ : U₀ ⋙ V₀ ≅ W₀) (b₃ : U₃ ⋙ V₃ ≅ W₃)
    (hL : ∀ M, V₃.map ((composeComparison eF eG).hom.app M) ≫
      (composeComparison dF dG).hom.app (U₀.obj M) ≫
      (F'' ⋙ G'').map (b₀.hom.app M) =
        b₃.hom.app ((F ⋙ G).obj M) ≫ (composeComparison qF qG).hom.app M)
    (hR : ∀ M, V₃.map ((composeComparison eH eI).hom.app M) ≫
      (composeComparison dH dI).hom.app (U₀.obj M) ≫
      (H'' ⋙ I'').map (b₀.hom.app M) =
        b₃.hom.app ((H ⋙ I).obj M) ≫ (composeComparison qH qI).hom.app M)
    (hq : ∀ M, W₃.map (a.app M) ≫ qI.hom.app (H.obj M) ≫ I''.map (qH.hom.app M) =
      qG.hom.app (F.obj M) ≫ G''.map (qF.hom.app M) ≫ a''.app (W₀.obj M))
    (hd : ∀ N, V₃.map (a'.app N) ≫ dI.hom.app (H'.obj N) ≫ I''.map (dH.hom.app N) =
      dG.hom.app (F'.obj N) ≫ G''.map (dF.hom.app N) ≫ a''.app (V₀.obj N)) (M : A) :
    V₃.map (U₃.map (a.app M) ≫ eI.hom.app (H.obj M) ≫ I'.map (eH.hom.app M)) =
      V₃.map (eG.hom.app (F.obj M) ≫ G'.map (eF.hom.app M) ≫ a'.app (U₀.obj M)) := by
  have hh := evaluated_cube a a' a''
    (composeComparison eF eG) (composeComparison eH eI)
    (composeComparison dF dG) (composeComparison dH dI)
    (composeComparison qF qG) (composeComparison qH qI) b₀ b₃ hL hR
    (fun N ↦ by simpa only [composeComparison_app, Category.assoc] using hq N)
    (fun N ↦ by simpa only [composeComparison_app, Category.assoc] using hd N) M
  simpa only [composeComparison_app, Category.assoc] using hh

private theorem transport_cube
    {A B D F A' B' D' F' : Type*}
    [Category A] [Category B] [Category D] [Category F]
    [Category A'] [Category B'] [Category D'] [Category F']
    (r r' : A ⥤ D) (p p' : B ⥤ F) (k k' : A ⥤ B) (i i' : D ⥤ F)
    (r₁ : A' ⥤ D') (p₁ : B' ⥤ F') (k₁ : A' ⥤ B') (i₁ : D' ⥤ F')
    (a : B ⥤ B') (b : F ⥤ F') (c : D ⥤ D') (d : A ⥤ A')
    (g : r ⋙ i ⟶ k ⋙ p) (g' : r' ⋙ i' ⟶ k' ⋙ p')
    (g₁ : r₁ ⋙ i₁ ⟶ k₁ ⋙ p₁)
    (ep : p ⋙ b ⟶ a ⋙ p₁) (ep' : p' ⋙ b ⟶ a ⋙ p₁)
    (er : r ⋙ c ⟶ d ⋙ r₁) (er' : r' ⋙ c ⟶ d ⋙ r₁)
    (bk : k ⋙ a ⟶ d ⋙ k₁) (bk' : k' ⋙ a ⟶ d ⋙ k₁)
    (bi : i ⋙ b ⟶ c ⋙ i₁) (bi' : i' ⋙ b ⟶ c ⋙ i₁)
    (hr : r = r') (hp : p = p') (hk : k = k') (hi : i = i')
    (hg : HEq g g') (hep : HEq ep ep') (her : HEq er er')
    (hbk : HEq bk bk') (hbi : HEq bi bi')
    (h : ∀ M, b.map (g'.app M) ≫ ep'.app (k'.obj M) ≫ p₁.map (bk'.app M) =
      bi'.app (r'.obj M) ≫ i₁.map (er'.app M) ≫ g₁.app (d.obj M)) (M : A) :
    b.map (g.app M) ≫ ep.app (k.obj M) ≫ p₁.map (bk.app M) =
      bi.app (r.obj M) ≫ i₁.map (er.app M) ≫ g₁.app (d.obj M) := by
  subst r'
  subst p'
  subst k'
  subst i'
  cases hg
  cases hep
  cases her
  cases hbk
  cases hbi
  exact h M

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (n : ℕ)
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf alpha gamma
set_option synthInstance.maxSize 4096
attribute [local irreducible] Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap
  Functor.rightDerivedFunctorIsoMapDerivedCategory
attribute [local implicit_reducible] VaryingRing.coefficientTransition
  StrictTower.G StrictTower.R P R

private local instance (priority := 50000) fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

private local instance (priority := 50000) fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private local instance (priority := 40000) fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt inferInstance
    (ProEt.topology X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

attribute [local instance 30000] StrictTower.clopenTowerAbelian
attribute [local instance 20000] StrictTower.towers_hasDerivedCategory
  proEtaleRingModules_hasDerivedCategory


private local instance levelTower_additive (X : Scheme.{u}) :
    (levelTower C τ n X).Additive := by
  dsimp only [levelTower]
  infer_instance

private local instance levelTower_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (levelTower C τ n X) := by
  dsimp only [levelTower]
  infer_instance

private local instance levelTower_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (levelTower C τ n X) := by
  dsimp only [levelTower]
  infer_instance

private def normalizedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    VaryingRing.G.{u} C τ f ⋙ E C τ n X ≅ E C τ n Y ⋙ StrictTower.G.{u} (C n) f :=
  Functor.mapDerivedCategorySquareIso
    (SemilinearProperOpenCoreAliases.constant_diagram_square
      (VaryingRing.pull.{u} C τ f) (VaryingRing.eval.{u} C τ X n)
      (VaryingRing.eval.{u} C τ Y n) (StrictTower.modulePullback.{u} (C n) f)
      (VaryingRing.moduleEvalG.{u} C τ f n))

set_option maxHeartbeats 800000 in
-- Comparing chosen ordinary adjoints requires additional normalization.
private theorem pullIso_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint] [F.Additive]
    [F.leftAdjoint.Additive] [PreservesFiniteLimits F.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint]
    (hF : F = VaryingRing.push.{u} C τ f)
    (e : levelTower C τ n X ⋙ StrictTower.towerDirectImage.{u} (C n) f ≅
      F ⋙ levelTower C τ n Y)
    (he : ∀ (M : Modules C τ X) (m : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op m)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x))
    (s : levelTower C τ n Y ⋙ StrictTower.towerPullback.{u} (C n) f ≅
      F.leftAdjoint ⋙ levelTower C τ n X)
    (hs : s.hom = (mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction f (StrictTower.coefficients.{u} (C n) Y)
        (StrictTower.coefficients.{u} (C n) X)
        (StrictTower.constantRingIso.{u} (C n) f)).whiskerRight ℕᵒᵖ)).symm e.inv) :
    HEq (Functor.mapDerivedCategorySquareIso s).inv (normalizedPull C τ n f).hom := by
  subst F
  let G := SemilinearProperOpenCoreAliases.constant_diagram_square
    (VaryingRing.pull.{u} C τ f) (VaryingRing.eval.{u} C τ X n)
    (VaryingRing.eval.{u} C τ Y n) (StrictTower.modulePullback.{u} (C n) f)
    (VaryingRing.moduleEvalG.{u} C τ f n)
  have hs' : s = G.symm := by
    apply Iso.ext
    rw [hs]
    exact eval_pull_mate_normalization C τ n f e he
  rw [hs']
  exact (Functor.square_symm_hom G.symm).symm.heq

private theorem evalP_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (evalP C τ n f).hom (normalizedPull C τ n f).hom := by
  let s := @asIso _ _ _ _ (evalPullInv C τ n f) (evalPullInv_isIso C τ n f)
  have hp : (evalP C τ n f).hom = (Functor.mapDerivedCategorySquareIso s).inv := by
    exact Functor.square_symm_hom s
  rw [hp]
  exact pullIso_normalized C τ n f (push C τ f) (push_eq C τ f)
    (evalPushOrdinary_existsUnique C τ n f).choose
    (evalPushOrdinary_existsUnique C τ n f).choose_spec.1 s rfl

private def ordinaryEvaluationBridge (X : Scheme.{u}) :
    levelTower C τ n X ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules.{u} (C n) X)).obj (op 0) ≅
      VaryingRing.eval.{u} C τ X n :=
  Iso.refl _

private def evaluationBridge (X : Scheme.{u}) :
    E C τ n X ⋙ StrictTower.ev.{u} (C n) X 0 ≅ VaryingRing.ev.{u} C τ X n :=
  (Functor.mapDerivedCategoryCompIso
    (C := Modules C τ X) (D := StrictTower.Towers.{u} (C n) X)
    (E := StrictTower.Modules.{u} (C n) X) (levelTower C τ n X)
    ((CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules.{u} (C n) X)).obj (op 0))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (C := Modules C τ X) (D := StrictTower.Modules.{u} (C n) X)
      (ordinaryEvaluationBridge C τ n X)

private theorem normalizedPull_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : VaryingRing.Derived.{u} C τ Y) :
    (StrictTower.ev.{u} (C n) X 0).map ((normalizedPull C τ n f).hom.app M) ≫
        (StrictTower.evalG.{u} (C n) f 0).hom.app ((E C τ n Y).obj M) ≫
        (StrictTower.modulePullback.{u} (C n) f).mapDerivedCategory.map
          ((evaluationBridge C τ n Y).hom.app M) =
      (evaluationBridge C τ n X).hom.app ((VaryingRing.G.{u} C τ f).obj M) ≫
        (VaryingRing.evalG.{u} C τ f n).hom.app M := by
  have : (VaryingRing.pull.{u} C τ f).Additive := VaryingRing.pullAdditive C τ f
  have : PreservesFiniteLimits (VaryingRing.pull.{u} C τ f) :=
    VaryingRing.pullLimits C τ f
  have : PreservesFiniteColimits (VaryingRing.pull.{u} C τ f) :=
    VaryingRing.pullColimits C τ f
  exact constant_evaluation (VaryingRing.pull.{u} C τ f)
    (VaryingRing.eval.{u} C τ X n) (VaryingRing.eval.{u} C τ Y n)
    (StrictTower.modulePullback.{u} (C n) f) (VaryingRing.moduleEvalG.{u} C τ f n) M

private def normalizedOpenInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    E C τ n U ⋙ StrictTower.J.{u} (C n) j ⟶ VaryingRing.J.{u} C τ j ⋙ E C τ n X :=
  ((mateEquiv (VaryingRing.jAdj.{u} C τ j) (StrictTower.jAdj.{u} (C n) j)).symm
    (TwoSquare.mk _ _ _ _ (normalizedPull C τ n j).hom)).natTrans

private theorem evalJInv_normalized {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    HEq (evalJInv C τ n j) (normalizedOpenInv C τ n j) := by
  exact inverse_mate_heq (jAdj C τ j) (VaryingRing.jAdj.{u} C τ j)
    (StrictTower.jAdj.{u} (C n) j) (StrictTower.jAdj.{u} (C n) j)
    (evalP C τ n j).hom (normalizedPull C τ n j).hom
    (J_eq C τ j) (P_eq C τ j) rfl rfl rfl rfl
    (Normalization.jadj_heq C τ j) HEq.rfl (evalP_normalized C τ n j)

private theorem normalizedOpenInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (normalizedOpenInv C τ n j) := by
  let _ := evalJInv_isIso C τ n j
  exact SemilinearProperOpenCoreAliases.isIso_of_heq
    (congrArg (fun F ↦ F ⋙ E C τ n X) (J_eq C τ j).symm)
    (normalizedOpenInv C τ n j) (evalJInv C τ n j)
    (evalJInv_normalized C τ n j).symm

private def normalizedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    VaryingRing.J.{u} C τ j ⋙ E C τ n X ≅ E C τ n U ⋙ StrictTower.J.{u} (C n) j :=
  (@asIso _ _ _ _ (normalizedOpenInv C τ n j) (normalizedOpenInv_isIso C τ n j)).symm

private theorem evalJ_normalized {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : HEq (evalJ C τ n j).hom (normalizedOpen C τ n j).hom := by
  apply iso_hom_of_inv_heq (evalJ C τ n j) (normalizedOpen C τ n j)
    (congrArg (fun F ↦ F ⋙ E C τ n X) (J_eq C τ j)) rfl
  exact evalJInv_normalized C τ n j

private theorem normalizedOpen_evaluation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : VaryingRing.Derived.{u} C τ U) :
    (StrictTower.ev.{u} (C n) X 0).map ((normalizedOpen C τ n j).hom.app M) ≫
        (StrictTower.evalJ.{u} (C n) j 0).hom.app ((E C τ n U).obj M) ≫
        (StrictTower.moduleJ.{u} (C n) j).mapDerivedCategory.map
          ((evaluationBridge C τ n U).hom.app M) =
      (evaluationBridge C τ n X).hom.app ((VaryingRing.J.{u} C τ j).obj M) ≫
        (VaryingRing.evalJ.{u} C τ j n).hom.app M := by
  exact inverse_mate_evaluation
    (VaryingRing.jAdj.{u} C τ j) (StrictTower.jAdj.{u} (C n) j)
    (VaryingRing.levelJAdj.{u} C j n)
    (normalizedPull C τ n j) (StrictTower.evalG.{u} (C n) j 0)
    (VaryingRing.evalG.{u} C τ j n)
    (normalizedOpen C τ n j) (StrictTower.evalJ.{u} (C n) j 0)
    (VaryingRing.evalJ.{u} C τ j n) rfl
    (inverse_mate_of_mate (StrictTower.jAdj.{u} (C n) j)
      (VaryingRing.levelJAdj.{u} C j n) (StrictTower.evalJ.{u} (C n) j 0).inv
      (StrictTower.evalG.{u} (C n) j 0).hom (VaryingRing.strictOpen_mate C n j)) rfl
    (evaluationBridge C τ n U) (evaluationBridge C τ n X)
    (normalizedPull_evaluation C τ n j) M

private theorem evaluation_injective (X : Scheme.{u})
    {A B : VaryingRing.Derived.{u} C τ X} {Z : StrictTower.Derived.{u} (C n) X}
    (e : (E C τ n X).obj B ≅ Z)
    {f g : (E C τ n X).obj A ⟶ Z}
    (h : (StrictTower.ev.{u} (C n) X 0).map f = (StrictTower.ev.{u} (C n) X 0).map g) :
    f = g := by
  let D := StrictTower.ConstantNormalization.delta (C n) X
  have : (Functor.const ℕᵒᵖ : StrictTower.Modules.{u} (C n) X ⥤
      StrictTower.Towers.{u} (C n) X).rightDerivedFunctor.Full := inferInstance
  have : D.Full := Functor.Full.of_iso
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (Functor.const ℕᵒᵖ : StrictTower.Modules.{u} (C n) X ⥤
        StrictTower.Towers.{u} (C n) X))
  let d : E C τ n X ≅ VaryingRing.ev.{u} C τ X n ⋙ D :=
    Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2} (VaryingRing.eval.{u} C τ X n) (Functor.const ℕᵒᵖ)
  apply (cancel_mono e.inv).mp
  apply (cancel_epi (d.inv.app A)).mp
  apply (cancel_mono (d.hom.app B)).mp
  apply map_injective_on_full_image D (StrictTower.ev.{u} (C n) X 0)
    (StrictTower.ConstantNormalization.deltaEval (C n) X 0)
  simp only [Functor.map_comp, h]

private theorem normalized_evaluation_injective
    {V W S : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) [IsOpenImmersion k]
    (M : VaryingRing.Derived.{u} C τ S) (N : VaryingRing.Derived.{u} C τ W)
    {f g : (E C τ n W).obj N ⟶
      (StrictTower.J.{u} (C n) k).obj
        ((StrictTower.G.{u} (C n) r).obj ((E C τ n S).obj M))}
    (h : (StrictTower.ev.{u} (C n) W 0).map f =
      (StrictTower.ev.{u} (C n) W 0).map g) : f = g := by
  exact evaluation_injective C τ n W
    (A := N)
    (B := (VaryingRing.J.{u} C τ k).obj ((VaryingRing.G.{u} C τ r).obj M))
    ((composeComparison (normalizedPull C τ n r) (normalizedOpen C τ n k)).app M) h

private theorem normalizedLeft_evaluation
    {W S T : Scheme.{u}} (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion i]
    (M : VaryingRing.Derived.{u} C τ S) :
    (StrictTower.ev.{u} (C n) W 0).map
        ((composeComparison (normalizedOpen C τ n i)
          (normalizedPull C τ n p)).hom.app M) ≫
      (composeComparison (StrictTower.evalJ.{u} (C n) i 0)
        (StrictTower.evalG.{u} (C n) p 0)).hom.app ((E C τ n S).obj M) ≫
      ((StrictTower.moduleJ.{u} (C n) i).mapDerivedCategory ⋙
        (StrictTower.modulePullback.{u} (C n) p).mapDerivedCategory).map
          ((evaluationBridge C τ n S).hom.app M) =
    (evaluationBridge C τ n W).hom.app
        (((VaryingRing.J.{u} C τ i) ⋙ VaryingRing.G.{u} C τ p).obj M) ≫
      (composeComparison (VaryingRing.evalJ.{u} C τ i n)
        (VaryingRing.evalG.{u} C τ p n)).hom.app M := by
  exact comparison_path (normalizedOpen C τ n i) (normalizedPull C τ n p)
    (StrictTower.evalJ.{u} (C n) i 0) (StrictTower.evalG.{u} (C n) p 0)
    (VaryingRing.evalJ.{u} C τ i n) (VaryingRing.evalG.{u} C τ p n)
    (evaluationBridge C τ n S) (evaluationBridge C τ n T)
    (evaluationBridge C τ n W)
    (normalizedOpen_evaluation C τ n i) (normalizedPull_evaluation C τ n p) M

private theorem normalizedRight_evaluation
    {V W S : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) [IsOpenImmersion k]
    (M : VaryingRing.Derived.{u} C τ S) :
    (StrictTower.ev.{u} (C n) W 0).map
        ((composeComparison (normalizedPull C τ n r)
          (normalizedOpen C τ n k)).hom.app M) ≫
      (composeComparison (StrictTower.evalG.{u} (C n) r 0)
        (StrictTower.evalJ.{u} (C n) k 0)).hom.app ((E C τ n S).obj M) ≫
      ((StrictTower.modulePullback.{u} (C n) r).mapDerivedCategory ⋙
        (StrictTower.moduleJ.{u} (C n) k).mapDerivedCategory).map
          ((evaluationBridge C τ n S).hom.app M) =
    (evaluationBridge C τ n W).hom.app
        (((VaryingRing.G.{u} C τ r) ⋙ VaryingRing.J.{u} C τ k).obj M) ≫
      (composeComparison (VaryingRing.evalG.{u} C τ r n)
        (VaryingRing.evalJ.{u} C τ k n)).hom.app M := by
  exact comparison_path (normalizedPull C τ n r) (normalizedOpen C τ n k)
    (StrictTower.evalG.{u} (C n) r 0) (StrictTower.evalJ.{u} (C n) k 0)
    (VaryingRing.evalG.{u} C τ r n) (VaryingRing.evalJ.{u} C τ k n)
    (evaluationBridge C τ n S) (evaluationBridge C τ n V)
    (evaluationBridge C τ n W)
    (normalizedPull_evaluation C τ n r) (normalizedOpen_evaluation C τ n k) M

private theorem normalized_cube_of_evaluation
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (v : VaryingRing.J.{u} C τ i ⋙ VaryingRing.G.{u} C τ p ⟶
      VaryingRing.G.{u} C τ r ⋙ VaryingRing.J.{u} C τ k)
    (t : StrictTower.J.{u} (C n) i ⋙ StrictTower.G.{u} (C n) p ⟶
      StrictTower.G.{u} (C n) r ⋙ StrictTower.J.{u} (C n) k)
    (a : (StrictTower.moduleJ.{u} (C n) i).mapDerivedCategory ⋙
        (StrictTower.modulePullback.{u} (C n) p).mapDerivedCategory ⟶
      (StrictTower.modulePullback.{u} (C n) r).mapDerivedCategory ⋙
        (StrictTower.moduleJ.{u} (C n) k).mapDerivedCategory)
    (ha : ∀ N : VaryingRing.Derived.{u} C τ S,
      (VaryingRing.ev.{u} C τ W n).map (v.app N) ≫
          (VaryingRing.evalJ.{u} C τ k n).hom.app ((VaryingRing.G.{u} C τ r).obj N) ≫
          (StrictTower.moduleJ.{u} (C n) k).mapDerivedCategory.map
            ((VaryingRing.evalG.{u} C τ r n).hom.app N) =
        (VaryingRing.evalG.{u} C τ p n).hom.app ((VaryingRing.J.{u} C τ i).obj N) ≫
          (StrictTower.modulePullback.{u} (C n) p).mapDerivedCategory.map
            ((VaryingRing.evalJ.{u} C τ i n).hom.app N) ≫
          a.app ((VaryingRing.ev.{u} C τ S n).obj N))
    (hs : ∀ N : StrictTower.Derived.{u} (C n) S,
      (StrictTower.ev.{u} (C n) W 0).map (t.app N) ≫
          (StrictTower.evalJ.{u} (C n) k 0).hom.app
            ((StrictTower.G.{u} (C n) r).obj N) ≫
          (StrictTower.moduleJ.{u} (C n) k).mapDerivedCategory.map
            ((StrictTower.evalG.{u} (C n) r 0).hom.app N) =
        (StrictTower.evalG.{u} (C n) p 0).hom.app
            ((StrictTower.J.{u} (C n) i).obj N) ≫
          (StrictTower.modulePullback.{u} (C n) p).mapDerivedCategory.map
            ((StrictTower.evalJ.{u} (C n) i 0).hom.app N) ≫
          a.app ((StrictTower.ev.{u} (C n) S 0).obj N))
    (M : VaryingRing.Derived.{u} C τ S) :
    (E C τ n W).map (v.app M) ≫
        (normalizedOpen C τ n k).hom.app ((VaryingRing.G.{u} C τ r).obj M) ≫
        (StrictTower.J.{u} (C n) k).map ((normalizedPull C τ n r).hom.app M) =
      (normalizedPull C τ n p).hom.app ((VaryingRing.J.{u} C τ i).obj M) ≫
        (StrictTower.G.{u} (C n) p).map ((normalizedOpen C τ n i).hom.app M) ≫
        t.app ((E C τ n S).obj M) := by
  apply normalized_evaluation_injective C τ n k r M
    ((VaryingRing.G.{u} C τ p).obj ((VaryingRing.J.{u} C τ i).obj M))
  exact expanded_evaluated_cube
    (F := VaryingRing.J.{u} C τ i) (G := VaryingRing.G.{u} C τ p)
    (H := VaryingRing.G.{u} C τ r) (I := VaryingRing.J.{u} C τ k)
    (F' := StrictTower.J.{u} (C n) i) (G' := StrictTower.G.{u} (C n) p)
    (H' := StrictTower.G.{u} (C n) r) (I' := StrictTower.J.{u} (C n) k)
    (F'' := (StrictTower.moduleJ.{u} (C n) i).mapDerivedCategory)
    (G'' := (StrictTower.modulePullback.{u} (C n) p).mapDerivedCategory)
    (H'' := (StrictTower.modulePullback.{u} (C n) r).mapDerivedCategory)
    (I'' := (StrictTower.moduleJ.{u} (C n) k).mapDerivedCategory)
    (U₀ := E C τ n S) (U₁ := E C τ n T) (U₂ := E C τ n V) (U₃ := E C τ n W)
    (V₀ := StrictTower.ev.{u} (C n) S 0) (V₁ := StrictTower.ev.{u} (C n) T 0)
    (V₂ := StrictTower.ev.{u} (C n) V 0) (V₃ := StrictTower.ev.{u} (C n) W 0)
    (W₀ := VaryingRing.ev.{u} C τ S n) (W₁ := VaryingRing.ev.{u} C τ T n)
    (W₂ := VaryingRing.ev.{u} C τ V n) (W₃ := VaryingRing.ev.{u} C τ W n)
    v t a
    (normalizedOpen C τ n i) (normalizedPull C τ n p)
    (normalizedPull C τ n r) (normalizedOpen C τ n k)
    (StrictTower.evalJ.{u} (C n) i 0) (StrictTower.evalG.{u} (C n) p 0)
    (StrictTower.evalG.{u} (C n) r 0) (StrictTower.evalJ.{u} (C n) k 0)
    (VaryingRing.evalJ.{u} C τ i n) (VaryingRing.evalG.{u} C τ p n)
    (VaryingRing.evalG.{u} C τ r n) (VaryingRing.evalJ.{u} C τ k n)
    (evaluationBridge C τ n S) (evaluationBridge C τ n W)
    (normalizedLeft_evaluation C τ n p i) (normalizedRight_evaluation C τ n k r)
    ha hs M

private theorem intrinsic_cube_of_normalized
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (a : J C τ i ⋙ P C τ p ⟶ P C τ r ⋙ J C τ k)
    (a' : VaryingRing.J.{u} C τ i ⋙ VaryingRing.G.{u} C τ p ⟶
      VaryingRing.G.{u} C τ r ⋙ VaryingRing.J.{u} C τ k)
    (a'' : StrictTower.J (C n) i ⋙ StrictTower.G (C n) p ⟶
      StrictTower.G (C n) r ⋙ StrictTower.J (C n) k)
    (hα : HEq a a')
    (hh : ∀ M : VaryingRing.Derived.{u} C τ S,
      (E C τ n W).map (a'.app M) ≫
          (normalizedOpen C τ n k).hom.app ((VaryingRing.G.{u} C τ r).obj M) ≫
          (StrictTower.J (C n) k).map ((normalizedPull C τ n r).hom.app M) =
        (normalizedPull C τ n p).hom.app ((VaryingRing.J.{u} C τ i).obj M) ≫
          (StrictTower.G (C n) p).map ((normalizedOpen C τ n i).hom.app M) ≫
          a''.app ((E C τ n S).obj M)) (M : Derived C τ S) :
    (E C τ n W).map (a.app M) ≫
        (evalJ C τ n k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J (C n) k).map ((evalP C τ n r).hom.app M) =
      (evalP C τ n p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G (C n) p).map ((evalJ C τ n i).hom.app M) ≫
        a''.app ((E C τ n S).obj M) := by
  have htransport := transport_cube
    (J C τ i) (VaryingRing.J.{u} C τ i) (J C τ k) (VaryingRing.J.{u} C τ k)
    (P C τ r) (VaryingRing.G.{u} C τ r) (P C τ p) (VaryingRing.G.{u} C τ p)
    (StrictTower.J (C n) i) (StrictTower.J (C n) k)
    (StrictTower.G (C n) r) (StrictTower.G (C n) p)
    (E C τ n V) (E C τ n W) (E C τ n T) (E C τ n S)
    a a'
    a''
    (evalJ C τ n k).hom (normalizedOpen C τ n k).hom
    (evalJ C τ n i).hom (normalizedOpen C τ n i).hom
    (evalP C τ n r).hom (normalizedPull C τ n r).hom
    (evalP C τ n p).hom (normalizedPull C τ n p).hom
    (J_eq C τ i) (J_eq C τ k) (P_eq C τ r) (P_eq C τ p)
    hα (evalJ_normalized C τ n k) (evalJ_normalized C τ n i)
    (evalP_normalized C τ n r) (evalP_normalized C τ n p)
    hh M
  exact htransport

private theorem intrinsicAlpha_normalized
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    HEq (alpha C τ k r p i h) (VaryingRing.alpha.{u} C τ k r p i h) := by
  exact (Normalization.system_alpha_localized C τ k r p i h).symm

attribute [local irreducible] VaryingRing.alpha StrictTower.alpha

set_option maxHeartbeats 800000 in
-- The categorical cube specializes six exact derived paths.
private theorem normalized_compatibility
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : VaryingRing.Derived.{u} C τ S) :
    (E C τ n W).map ((VaryingRing.alpha.{u} C τ k r p i h).app M) ≫
        (normalizedOpen C τ n k).hom.app ((VaryingRing.G.{u} C τ r).obj M) ≫
        (StrictTower.J.{u} (C n) k).map ((normalizedPull C τ n r).hom.app M) =
      (normalizedPull C τ n p).hom.app ((VaryingRing.J.{u} C τ i).obj M) ≫
        (StrictTower.G.{u} (C n) p).map ((normalizedOpen C τ n i).hom.app M) ≫
        (StrictTower.alpha.{u} (C n) k r p i h).app ((E C τ n S).obj M) := by
  refine Exists.elim (VaryingRing.clopenArrowEvaluation.{u} C τ k r p i h n) fun a hh ↦ ?_
  have hcube := normalized_cube_of_evaluation C τ n k r p i
    (VaryingRing.alpha.{u} C τ k r p i h) (StrictTower.alpha.{u} (C n) k r p i h)
    a hh.1 hh.2 M
  exact hcube

set_option maxHeartbeats 800000 in
-- The dependent transport retains the four specified chosen-adjoint comparisons.
/-- Evaluation preserves the specified inverse-image alpha word, before taking proper mates.
Source: Stacks Project, Tags 03DI and 0F7B; Zheng, Construction 4.1 and Lemma 4.10.
Proof: normalize the specified intrinsic inverse-image and open comparisons to
those of the varying-ring operations. Exact-square composition identifies their
composites with evaluation at zero and varying-ring evaluation at n; inverse-mate
pasting gives the corresponding open-extension identity. Apply the two equations
of clopenArrowEvaluation to the common single-level alpha transformation. Naturality
of the path comparisons and the evaluation identifications gives the required
cube after evaluation at zero. Both endpoints, after the invertible output-path
comparison, lie in the image of the derived constant diagonal. That diagonal is
full and its composite with evaluation is the identity, so evaluation is injective
on these maps. Finally transport the cube along the intrinsic/varying-ring
normalization equalities. This argument allows empty schemes, zero coefficient
rings, arbitrary transitions, and noncartesian proper/open squares, and assumes
no faithfulness of evaluation on arbitrary derived towers.
(blueprint: lem-sf-intrinsic-evaluation-alpha-compatibility). -/
theorem intrinsicEvaluationAlphaCompatibility
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (E C τ n W).map ((alpha C τ k r p i h).app M) ≫
        (evalJ C τ n k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J (C n) k).map ((evalP C τ n r).hom.app M) =
      (evalP C τ n p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G (C n) p).map ((evalJ C τ n i).hom.app M) ≫
        (StrictTower.alpha (C n) k r p i h).app ((E C τ n S).obj M) := by
  have hfinal := intrinsic_cube_of_normalized C τ n k r p i
    (alpha C τ k r p i h) (VaryingRing.alpha.{u} C τ k r p i h)
    (StrictTower.alpha (C n) k r p i h)
    (intrinsicAlpha_normalized C τ k r p i h) (normalized_compatibility C τ n k r p i h) M
  exact hfinal

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
