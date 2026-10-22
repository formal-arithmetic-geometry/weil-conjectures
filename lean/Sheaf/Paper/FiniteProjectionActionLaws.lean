/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal

/-!
# Tensor-action and open-counit identities for finite-level projection maps

Source: blueprint sec-smooth-purity, lem-pur-projection-purity-agreement, expanded Step 6;
Stacks Project Tags 0B56, 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).

The eight statements give the proper, open, open-counit and chosen-compactification
identities on each of the pro-etale and ordinary etale sites. All projection maps are
actual canonical maps, with no invertibility, boundedness or constructibility assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

private theorem projection_counit
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {Q : D ⥤ C} (adj : J ⊣ Q)
    (S : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj Q).obj S).obj T ⟶
      (Functor.postcompose₂.obj Q).obj T') (F N : D) :
    J.map ((δ.app F).app N) ≫ adj.counit.app ((T'.obj F).obj N) =
      ((adj.projectionMap S T T' δ).app (Q.obj F)).app N ≫
        (T'.map (adj.counit.app F)).app N := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  have hp := adj.unit_app_comp_map_projectionMap_app_app S T T' δ (Q.obj F) N
  dsimp [Adjunction.projectionMapTranspose] at hp
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  change (δ.app F).app N ≫ adj.unit.app (Q.obj ((T'.obj F).obj N)) ≫
      Q.map (adj.counit.app _) =
    (adj.unit.app ((T.obj (Q.obj F)).obj (S.obj N)) ≫
      Q.map (((adj.projectionMap S T T' δ).app (Q.obj F)).app N)) ≫
        Q.map ((T'.map (adj.counit.app F)).app N)
  rw [hp]
  have hn := congr_app (δ.naturality (adj.counit.app F)) N
  dsimp at hn
  rw [Category.assoc, ← hn, ← NatTrans.comp_app_assoc, ← T.map_comp]
  simp

private theorem projection_counit_iso
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {Q : D ⥤ C} (adj : J ⊣ Q)
    (S : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj Q).obj S).obj T ⟶
      (Functor.postcompose₂.obj Q).obj T') (F N : D)
    (p : J.obj ((T.obj (Q.obj F)).obj (S.obj N)) ≅ (T'.obj (J.obj (Q.obj F))).obj N)
    (hp : p.hom = ((adj.projectionMap S T T' δ).app (Q.obj F)).app N) :
    p.inv ≫ J.map ((δ.app F).app N) ≫ adj.counit.app ((T'.obj F).obj N) =
      (T'.map (adj.counit.app F)).app N := by
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp, hp]
  exact projection_counit adj S T T' δ F N

private theorem cancel_iso_map
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {U V W : C} {Z : D} (e : V ≅ W) (q : Z ⟶ H.obj V)
    (p : Z ⟶ H.obj U) (d : U ⟶ W)
    (h : q ≫ H.map e.hom = p ≫ H.map d) :
    p ≫ H.map (d ≫ e.inv) = q := by
  rw [H.map_comp, ← Category.assoc, ← h, Category.assoc,
    ← H.map_comp, Iso.hom_inv_id, H.map_id, Category.comp_id]

private theorem action_of_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (H : C ⥤ D) (S : D ⥤ C)
    (φ : ∀ N N' : D, S.obj (N ⊗ N') ⟶ S.obj N ⊗ S.obj N')
    (π : ∀ M N, H.obj M ⊗ N ⟶ H.obj (M ⊗ S.obj N))
    (M : C) (N N' : D)
    (h : π M N ▷ N' ≫ π (M ⊗ S.obj N) N' ≫
        H.map (α_ M (S.obj N) (S.obj N')).hom =
      (α_ (H.obj M) N N').hom ≫ π M (N ⊗ N') ≫ H.map (M ◁ φ N N')) :
    (α_ (H.obj M) N N').hom ≫ π M (N ⊗ N') ≫
      H.map (M ◁ φ N N' ≫ (α_ M (S.obj N) (S.obj N')).inv) =
        π M N ▷ N' ≫ π (M ⊗ S.obj N) N' := by
  have h' := congrArg (fun k ↦ k ≫ H.map (α_ M (S.obj N) (S.obj N')).inv) h
  simpa only [Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
    Category.comp_id] using h'.symm

private theorem inverse_action_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (J : C ⥤ D) (S : D ⥤ C)
    (d : ∀ N N' : D, S.obj (N ⊗ N') ⟶ S.obj N ⊗ S.obj N')
    [∀ N N', IsIso (d N N')]
    (p : ∀ M N, J.obj (M ⊗ S.obj N) ≅ J.obj M ⊗ N)
    (M : C) (N N' : D)
    (h₀ : J.map (α_ M (S.obj N) (S.obj N')).hom ≫
      J.map (M ◁ inv (d N N')) ≫ (p M (N ⊗ N')).hom ≫
        (α_ (J.obj M) N N').inv =
      (p (M ⊗ S.obj N) N').hom ≫ (p M N).hom ▷ N') :
    (p M N).inv ▷ N' ≫ (p (M ⊗ S.obj N) N').inv =
      (α_ _ _ _).hom ≫ (p M (N ⊗ N')).inv ≫
        J.map (M ◁ d N N' ≫ (α_ _ _ _).inv) := by
  have h : (p (M ⊗ S.obj N) N').hom ≫ (p M N).hom ▷ N' ≫
      (α_ _ _ _).hom =
    J.map ((α_ _ _ _).hom ≫ M ◁ inv (d N N')) ≫ (p M (N ⊗ N')).hom := by
    rw [← reassoc_of% h₀, Iso.inv_hom_id, Category.comp_id, J.map_comp, Category.assoc]
  rw [← cancel_mono ((p (M ⊗ S.obj N) N').hom ≫
    (p M N).hom ▷ N' ≫ (α_ _ _ _).hom)]
  simp only [Category.assoc]
  conv_rhs => rw [h]
  simp only [Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp, ← J.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp, IsIso.hom_inv_id,
    whiskerLeft_id]
  rw [J.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem projection_map_assoc_data
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C)
    (μ : ∀ M N, G'.obj M ⊗ G'.obj N ⟶ G'.obj (M ⊗ N))
    (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj G).obj (curriedTensor D))
    (hδ : ∀ (X : D) (M M' : D), (α_ (G.obj X) (G'.obj M) (G'.obj M')).hom ≫
      G.obj X ◁ μ M M' ≫ (δ.app X).app (M ⊗ M') ≫
        G.map (α_ X M M').inv = (δ.app X).app M ▷ G'.obj M' ≫ (δ.app (X ⊗ M)).app M')
    (K : C) (M M' : D) :
    F.map (α_ K (G'.obj M) (G'.obj M')).hom ≫ F.map (K ◁ μ M M') ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app (M ⊗ M') ≫
          (α_ (F.obj K) M M').inv =
      ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app (K ⊗ G'.obj M)).app M' ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ M' := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adj.unit_naturality_assoc, adj.unit_naturality_assoc]
  have h₁ := adj.unit_app_comp_map_projectionMap_app_app_assoc G' (curriedTensor C)
    (curriedTensor D) δ K (M ⊗ M') (G.map (α_ (F.obj K) M M').inv)
  have h₂ := adj.unit_app_comp_map_projectionMap_app_app_assoc G' (curriedTensor C)
    (curriedTensor D) δ (K ⊗ G'.obj M) M'
    (G.map (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ M'))
  dsimp [Adjunction.projectionMapTranspose] at h₁ h₂
  rw [h₁, h₂]
  have h₃ := congr_app (δ.naturality
    (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M)) M'
  have h₄ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C)
    (curriedTensor D) δ K M
  dsimp [Adjunction.projectionMapTranspose] at h₃ h₄
  simp only [Category.assoc]
  rw [← h₃, ← comp_whiskerRight_assoc, h₄, comp_whiskerRight_assoc, ← hδ,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]


private theorem inverse_comparison_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (S : C ⥤ D) (d : ∀ K M, S.obj (K ⊗ M) ≅ S.obj K ⊗ S.obj M)
    (h : ∀ K M N, (d (K ⊗ M) N).hom ≫ (d K M).hom ▷ S.obj N ≫
      (α_ _ _ _).hom = S.map (α_ K M N).hom ≫ (d K (M ⊗ N)).hom ≫
        S.obj K ◁ (d M N).hom) (K M N : C) :
    S.obj K ◁ (d M N).inv ≫ (d K (M ⊗ N)).inv ≫ S.map (α_ K M N).inv =
      (α_ _ _ _).inv ≫ (d K M).inv ▷ S.obj N ≫ (d (K ⊗ M) N).inv := by
  have ha : (d K M).inv ▷ S.obj N ≫ (d (K ⊗ M) N).inv ≫ S.map (α_ K M N).hom =
      (α_ _ _ _).hom ≫ S.obj K ◁ (d M N).inv ≫ (d K (M ⊗ N)).inv := by
    rw [← cancel_epi ((d K M).hom ▷ S.obj N), ← cancel_epi (d (K ⊗ M) N).hom,
      reassoc_of% (h K M N)]
    simp
  rw [Iso.eq_inv_comp, ← reassoc_of% ha, ← S.map_comp, Iso.hom_inv_id,
    S.map_id, Category.comp_id]

private theorem mixed_comparison_assoc
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (S Q : D ⥤ C) (e : S ≅ Q)
    (μ : ∀ M N, S.obj M ⊗ S.obj N ⟶ S.obj (M ⊗ N))
    (hm : ∀ K M N, S.obj K ◁ μ M N ≫ μ K (M ⊗ N) ≫ S.map (α_ K M N).inv =
      (α_ _ _ _).inv ≫ μ K M ▷ S.obj N ≫ μ (K ⊗ M) N)
    (d : ∀ K M, Q.obj K ⊗ S.obj M ⟶ Q.obj (K ⊗ M))
    (hd : ∀ K M, d K M = e.inv.app K ▷ S.obj M ≫
      μ K M ≫ e.hom.app (K ⊗ M)) (K M N : D) :
    (α_ (Q.obj K) (S.obj M) (S.obj N)).hom ≫
      Q.obj K ◁ μ M N ≫ d K (M ⊗ N) ≫
      Q.map (α_ K M N).inv =
        d K M ▷ S.obj N ≫ d (K ⊗ M) N := by
  simp only [hd, Category.assoc, comp_whiskerRight]
  rw [← e.hom.naturality,
    ← comp_whiskerRight_assoc (e.hom.app _), Iso.hom_inv_id_app,
    id_whiskerRight, Category.id_comp, whisker_exchange_assoc,
    ← associator_naturality_left_assoc, reassoc_of% (hm K M N),
    Iso.hom_inv_id_assoc]

private theorem tensor_comparison_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H T : C ⥤ E)
    (a : H ≅ T) (b : T ≅ F ⋙ G)
    (dF : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (dG : ∀ K M, G.obj (K ⊗ M) ⟶ G.obj K ⊗ G.obj M)
    (dH : ∀ K M, H.obj (K ⊗ M) ⟶ H.obj K ⊗ H.obj M)
    (dT : ∀ K M, T.obj (K ⊗ M) ⟶ T.obj K ⊗ T.obj M)
    (K M : C)
    (hn : a.hom.app (K ⊗ M) ≫ dT K M =
      dH K M ≫ (a.hom.app K ⊗ₘ a.hom.app M))
    (hc : G.map (dF K M) ≫ dG (F.obj K) (F.obj M) =
      b.inv.app (K ⊗ M) ≫ dT K M ≫ (b.hom.app K ⊗ₘ b.hom.app M)) :
    (a ≪≫ b).hom.app (K ⊗ M) ≫ G.map (dF K M) ≫ dG (F.obj K) (F.obj M) =
      dH K M ≫ ((a ≪≫ b).hom.app K ⊗ₘ (a ≪≫ b).hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [hc]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hn, Category.assoc, tensorHom_comp_tensorHom]

private theorem tensor_comparison_inverse
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (e : H ≅ F ⋙ G)
    (dF : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (dG : ∀ K M, G.obj (K ⊗ M) ⟶ G.obj K ⊗ G.obj M)
    (dH : ∀ K M, H.obj (K ⊗ M) ⟶ H.obj K ⊗ H.obj M)
    (K M : C)
    (h : e.hom.app (K ⊗ M) ≫ G.map (dF K M) ≫ dG (F.obj K) (F.obj M) =
      dH K M ≫ (e.hom.app K ⊗ₘ e.hom.app M)) :
    e.inv.app (K ⊗ M) ≫ dH K M =
      (G.map (dF K M) ≫ dG (F.obj K) (F.obj M)) ≫
        (e.inv.app K ⊗ₘ e.inv.app M) := by
  have ht := congrArg (fun k ↦ e.inv.app (K ⊗ M) ≫ k ≫
    (e.inv.app K ⊗ₘ e.inv.app M)) h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app, id_tensorHom_id, Category.comp_id] using ht.symm

namespace CategoryTheory.Functor
open _root_.DerivedCategory LaxMonoidal OplaxMonoidal
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type*} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [BraidedCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
omit [Abelian.HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] in
private theorem generic_resolutions (X : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩
@[instance_reducible]
private noncomputable def generic_oplax : F.leftDerivedFunctor.OplaxMonoidal :=
  have := _root_.DerivedCategory.isIso_ε_Qh D
  AlgebraicGeometry.Etale.ofLaxSquareHδ (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    F.leftDerivedTensorComparison_app_app_comp_tensorHom F.kFlatMap
    (generic_resolutions F) (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

private theorem generic_oplax_assoc (K M N : DerivedCategory C) :
    (F.leftDerivedTensorComparison.app (K ⊗ M)).app N ≫
      (F.leftDerivedTensorComparison.app K).app M ▷ F.leftDerivedFunctor.obj N ≫
        (α_ _ _ _).hom =
      F.leftDerivedFunctor.map (α_ K M N).hom ≫
        (F.leftDerivedTensorComparison.app K).app (M ⊗ N) ≫
        F.leftDerivedFunctor.obj K ◁ (F.leftDerivedTensorComparison.app M).app N := by
  let := generic_oplax F
  exact OplaxMonoidal.associativity F.leftDerivedFunctor K M N

private theorem generic_composite
    {E : Type*} [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
    [BraidedCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]
    (a : H ≅ F ⋙ G) [NatTrans.IsMonoidal a.hom] (K M : DerivedCategory C) :
    (H.leftDerivedFunctorNatIso a ≪≫ F.leftDerivedFunctorCompIso G).hom.app (K ⊗ M) ≫
        G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) =
      (H.leftDerivedTensorComparison.app K).app M ≫
        ((H.leftDerivedFunctorNatIso a ≪≫ F.leftDerivedFunctorCompIso G).hom.app K ⊗ₘ
          (H.leftDerivedFunctorNatIso a ≪≫ F.leftDerivedFunctorCompIso G).hom.app M) := by
  exact tensor_comparison_composite F.leftDerivedFunctor G.leftDerivedFunctor
    H.leftDerivedFunctor (F ⋙ G).leftDerivedFunctor
    (H.leftDerivedFunctorNatIso a) (F.leftDerivedFunctorCompIso G)
    (fun K M ↦ (F.leftDerivedTensorComparison.app K).app M)
    (fun K M ↦ (G.leftDerivedTensorComparison.app K).app M)
    (fun K M ↦ (H.leftDerivedTensorComparison.app K).app M)
    (fun K M ↦ ((F ⋙ G).leftDerivedTensorComparison.app K).app M) K M
    (leftDerivedTensorComparison_naturality_app a K M)
    (map_leftDerivedTensorComparison_app_app_comp F G K M)

end CategoryTheory.Functor


private noncomputable def composite_projection_components
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (G : E ⥤ D) (J : C ⥤ E) (F : D ⥤ E) {F' : E ⥤ C} {F'' : D ⥤ C}
    (π : ∀ K L, G.obj K ⊗ L ⟶ G.obj (K ⊗ F.obj L))
    (ψ : ∀ K N, J.obj K ⊗ N ⟶ J.obj (K ⊗ F'.obj N))
    (e : ∀ L, F'.obj (F.obj L) ⟶ F''.obj L) (K : C) (L : D) :
    (J ⋙ G).obj K ⊗ L ⟶ (J ⋙ G).obj (K ⊗ F''.obj L) :=
  π (J.obj K) L ≫ G.map (ψ K (F.obj L)) ≫ G.map (J.map (K ◁ e L))

private theorem composite_projection_components_action
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (G : E ⥤ D) (J : C ⥤ E) (F : D ⥤ E) {F' : E ⥤ C} {F'' : D ⥤ C}
    (π : ∀ K L, G.obj K ⊗ L ⟶ G.obj (K ⊗ F.obj L))
    (ψ : ∀ K N, J.obj K ⊗ N ⟶ J.obj (K ⊗ F'.obj N))
    (e : ∀ L, F'.obj (F.obj L) ⟶ F''.obj L)
    (φ : ∀ L L', F.obj (L ⊗ L') ⟶ F.obj L ⊗ F.obj L')
    (φ' : ∀ N N', F'.obj (N ⊗ N') ⟶ F'.obj N ⊗ F'.obj N')
    (φ'' : ∀ L L', F''.obj (L ⊗ L') ⟶ F''.obj L ⊗ F''.obj L')
    (hπl : ∀ {K K' : E} (x : K ⟶ K') (L : D),
      G.map x ▷ L ≫ π K' L = π K L ≫ G.map (x ▷ F.obj L))
    (hπ : ∀ K L L', (α_ (G.obj K) L L').hom ≫ π K (L ⊗ L') ≫
      G.map (K ◁ φ L L' ≫ (α_ K (F.obj L) (F.obj L')).inv) =
        π K L ▷ L' ≫ π (K ⊗ F.obj L) L')
    (hψl : ∀ {K K' : C} (x : K ⟶ K') (N : E),
      J.map x ▷ N ≫ ψ K' N = ψ K N ≫ J.map (x ▷ F'.obj N))
    (hψr : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      J.obj K ◁ y ≫ ψ K N' = ψ K N ≫ J.map (K ◁ F'.map y))
    (hψ : ∀ K N N', ψ K N ▷ N' ≫ ψ (K ⊗ F'.obj N) N' =
      (α_ _ _ _).hom ≫ ψ K (N ⊗ N') ≫ J.map (K ◁ φ' N N' ≫ (α_ _ _ _).inv))
    (he : ∀ L L', e (L ⊗ L') ≫ φ'' L L' =
      F'.map (φ L L') ≫ φ' _ _ ≫ (e L ⊗ₘ e L'))
    (K : C) (L L' : D) :
    (α_ ((J ⋙ G).obj K) L L').hom ≫
      composite_projection_components G J F π ψ e K (L ⊗ L') ≫
      (J ⋙ G).map (K ◁ φ'' L L' ≫ (α_ K (F''.obj L) (F''.obj L')).inv) =
        composite_projection_components G J F π ψ e K L ▷ L' ≫
          composite_projection_components G J F π ψ e (K ⊗ F''.obj L) L' := by
  apply action_of_assoc (J ⋙ G) F'' φ''
    (fun K L ↦ composite_projection_components G J F π ψ e K L) K L L'
  have h₁ := (hπ (J.obj K) L L').symm
  simp only [composite_projection_components, comp_whiskerRight,
    Category.assoc, CategoryTheory.Functor.comp_map]
  rw [reassoc_of% (hπl (J.map (K ◁ e L)) L'),
    reassoc_of% (hπl (ψ K (F.obj L)) L')]
  erw [reassoc_of% h₁]
  simp only [← G.map_comp]
  congr 3
  simp only [Category.assoc]
  rw [reassoc_of% (hψl (K ◁ e L) (F.obj L')),
    reassoc_of% (hψ K _ _), Iso.inv_hom_id_assoc]
  erw [reassoc_of% (hψr K (φ L L'))]
  simp only [← J.map_comp]
  congr 2
  rw [← MonoidalCategory.whiskerLeft_comp, he, MonoidalCategory.tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

private noncomputable def composite_projection_bifunctor
    {C D E : Type*} [Category C] [Category D] [Category E]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (TE : E ⥤ E ⥤ E)
    (G : E ⥤ D) (J : C ⥤ E) (F : D ⥤ E) {F' : E ⥤ C} {F'' : D ⥤ C}
    (π : ∀ K L, (TD.obj (G.obj K)).obj L ⟶ G.obj ((TE.obj K).obj (F.obj L)))
    (ψ : ∀ K N, (TE.obj (J.obj K)).obj N ⟶ J.obj ((TC.obj K).obj (F'.obj N)))
    (e : ∀ L, F'.obj (F.obj L) ⟶ F''.obj L) (K : C) (L : D) :
    (TD.obj ((J ⋙ G).obj K)).obj L ⟶ (J ⋙ G).obj ((TC.obj K).obj (F''.obj L)) :=
  π (J.obj K) L ≫ G.map (ψ K (F.obj L)) ≫ G.map (J.map ((TC.obj K).map (e L)))

private theorem composite_projection_bifunctor_action
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (TE : E ⥤ E ⥤ E)
    (hTC : TC = curriedTensor C) (hTD : TD = curriedTensor D)
    (hTE : TE = curriedTensor E)
    (aC : ∀ K M N, (TC.obj ((TC.obj K).obj M)).obj N ≅
      (TC.obj K).obj ((TC.obj M).obj N))
    (aD : ∀ K M N, (TD.obj ((TD.obj K).obj M)).obj N ≅
      (TD.obj K).obj ((TD.obj M).obj N))
    (aE : ∀ K M N, (TE.obj ((TE.obj K).obj M)).obj N ≅
      (TE.obj K).obj ((TE.obj M).obj N))
    (haC : HEq aC (fun K M N : C ↦ α_ K M N))
    (haD : HEq aD (fun K M N : D ↦ α_ K M N))
    (haE : HEq aE (fun K M N : E ↦ α_ K M N))
    (G : E ⥤ D) (J : C ⥤ E) (F : D ⥤ E) {F' : E ⥤ C} {F'' : D ⥤ C}
    (π : ∀ K L, (TD.obj (G.obj K)).obj L ⟶ G.obj ((TE.obj K).obj (F.obj L)))
    (ψ : ∀ K N, (TE.obj (J.obj K)).obj N ⟶ J.obj ((TC.obj K).obj (F'.obj N)))
    (e : ∀ L, F'.obj (F.obj L) ⟶ F''.obj L)
    (φ : ∀ L L', F.obj ((TD.obj L).obj L') ⟶ (TE.obj (F.obj L)).obj (F.obj L'))
    (φ' : ∀ N N', F'.obj ((TE.obj N).obj N') ⟶ (TC.obj (F'.obj N)).obj (F'.obj N'))
    (φ'' : ∀ L L', F''.obj ((TD.obj L).obj L') ⟶ (TC.obj (F''.obj L)).obj (F''.obj L'))
    (φ₀ : ∀ L L', F.obj (L ⊗ L') ⟶ F.obj L ⊗ F.obj L')
    (φ₁ : ∀ N N', F'.obj (N ⊗ N') ⟶ F'.obj N ⊗ F'.obj N')
    (φ₂ : ∀ L L', F''.obj (L ⊗ L') ⟶ F''.obj L ⊗ F''.obj L')
    (hφ₀ : HEq φ φ₀) (hφ₁ : HEq φ' φ₁) (hφ₂ : HEq φ'' φ₂)
    (hπl : ∀ {K K' : E} (x : K ⟶ K') (L : D),
      (TD.map (G.map x)).app L ≫ π K' L = π K L ≫ G.map ((TE.map x).app (F.obj L)))
    (hπ : ∀ K L L', (aD (G.obj K) L L').hom ≫ π K ((TD.obj L).obj L') ≫
      G.map ((TE.obj K).map (φ L L') ≫ (aE K (F.obj L) (F.obj L')).inv) =
        (TD.map (π K L)).app L' ≫ π ((TE.obj K).obj (F.obj L)) L')
    (hψl : ∀ {K K' : C} (x : K ⟶ K') (N : E),
      (TE.map (J.map x)).app N ≫ ψ K' N = ψ K N ≫ J.map ((TC.map x).app (F'.obj N)))
    (hψr : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      (TE.obj (J.obj K)).map y ≫ ψ K N' = ψ K N ≫ J.map ((TC.obj K).map (F'.map y)))
    (hψ : ∀ K N N', (TE.map (ψ K N)).app N' ≫ ψ ((TC.obj K).obj (F'.obj N)) N' =
      (aE (J.obj K) N N').hom ≫ ψ K ((TE.obj N).obj N') ≫
        J.map ((TC.obj K).map (φ' N N') ≫ (aC K (F'.obj N) (F'.obj N')).inv))
    (he : ∀ L L', e (L ⊗ L') ≫ φ₂ L L' =
      F'.map (φ₀ L L') ≫ φ₁ _ _ ≫ (e L ⊗ₘ e L'))
    (K : C) (L L' : D) :
    (aD ((J ⋙ G).obj K) L L').hom ≫
      composite_projection_bifunctor TC TD TE G J F π ψ e K ((TD.obj L).obj L') ≫
      (J ⋙ G).map ((TC.obj K).map (φ'' L L') ≫
        (aC K (F''.obj L) (F''.obj L')).inv) =
      (TD.map (composite_projection_bifunctor TC TD TE G J F π ψ e K L)).app L' ≫
        composite_projection_bifunctor TC TD TE G J F π ψ e
          ((TC.obj K).obj (F''.obj L)) L' := by
  subst TC
  subst TD
  subst TE
  have hc := eq_of_heq haC
  have hd := eq_of_heq haD
  have he' := eq_of_heq haE
  subst aC
  subst aD
  subst aE
  have hp₀ := eq_of_heq hφ₀
  have hp₁ := eq_of_heq hφ₁
  have hp₂ := eq_of_heq hφ₂
  subst φ₀
  subst φ₁
  subst φ₂
  simp only [curriedTensor_obj_obj, curriedTensor_obj_map, curriedTensor_map_app]
    at hπl hπ hψl hψr hψ he ⊢
  exact composite_projection_components_action G J F π ψ e φ φ' φ''
    hπl hπ hψl hψr hψ he K L L'

private def compositionComponent
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (F' : E ⥤ C) (F'' : D ⥤ C) (e : F ⋙ F' ≅ F'') (L : D) :
    F'.obj (F.obj L) ⟶ F''.obj L := e.hom.app L

private theorem compositionComponent_tensor
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) (F' : E ⥤ C) (F'' : D ⥤ C) (e : F ⋙ F' ≅ F'')
    (φ₀ : ∀ L L', F.obj (L ⊗ L') ⟶ F.obj L ⊗ F.obj L')
    (φ₁ : ∀ N N', F'.obj (N ⊗ N') ⟶ F'.obj N ⊗ F'.obj N')
    (φ₂ : ∀ L L', F''.obj (L ⊗ L') ⟶ F''.obj L ⊗ F''.obj L')
    (h : ∀ L L', e.hom.app (L ⊗ L') ≫ φ₂ L L' =
      F'.map (φ₀ L L') ≫ φ₁ _ _ ≫ (e.hom.app L ⊗ₘ e.hom.app L'))
    (L L' : D) :
    compositionComponent F F' F'' e (L ⊗ L') ≫ φ₂ L L' =
      F'.map (φ₀ L L') ≫ φ₁ _ _ ≫
        (compositionComponent F F' F'' e L ⊗ₘ compositionComponent F F' F'' e L') := by
  exact h L L'


namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the lifted positive-level quotient used in the projection identities.
Source: the finite coefficient convention and coefficient-extension finiteness
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable instance projectionAction_coefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  @Finite.of_equiv P.Coefficient P.Ring
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)
    Equiv.ulift.symm

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The canonical reassociation of the derived tensor bifunctor, exposed before
specializing the coefficient category to avoid comparing two monoidal instance terms.
Source: Stacks Tag 0FPT, reassociation on total tensors
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable def projectionActionAssociator
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((derivedTensor B X).obj (((derivedTensor B X).obj K).obj M)).obj N ≅
      ((derivedTensor B X).obj K).obj (((derivedTensor B X).obj M).obj N) :=
  α_ K M N

end AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.Etale.sheafBraidedCategory

section ActionTensor

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open DerivedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

private theorem actionTensor_comparison_eq :
    leftDerivedUpperStarTensorComparison A g = (g)^*[A].leftDerivedTensorComparison := by
  rfl

private theorem actionTensor_assoc
    (K M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((leftDerivedUpperStarTensorComparison A g).app (K ⊗ M)).app N ≫
      ((leftDerivedUpperStarTensorComparison A g).app K).app M ▷ L((g)^*[A]).obj N ≫
        (α_ _ _ _).hom =
      L((g)^*[A]).map (α_ K M N).hom ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app (M ⊗ N) ≫
        L((g)^*[A]).obj K ◁ ((leftDerivedUpperStarTensorComparison A g).app M).app N := by
  rw [actionTensor_comparison_eq]
  exact CategoryTheory.Functor.generic_oplax_assoc (g)^*[A] K M N

end ActionTensor

section ActionComposition

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {T S R : Scheme.{u}} (i : T ⟶ S) (g : S ⟶ R)

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] in
private theorem actionTensor_underived_comp :
    NatTrans.IsMonoidal (upperStarComp A i g).hom := by
  have : NatTrans.IsMonoidal (lowerStarComp A i g).hom := by
    unfold lowerStarComp
    infer_instance
  have h : (upperStarComp A i g).hom =
      (conjugateEquiv ((upperStarLowerStarAdjunction A g).comp
        (upperStarLowerStarAdjunction A i))
        (upperStarLowerStarAdjunction A (i ≫ g))).symm (lowerStarComp A i g).hom := by
    rw [Equiv.eq_symm_apply]
    exact conjugateEquiv_upperStarComp_hom A i g
  rw [h]
  exact isMonoidal_conjugateEquiv_symm _ _ _

omit [UpperStarPreservesFlat A] in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem actionTensor_compactification_eq_aux {T S R : Scheme.{u}}
    (i : T ⟶ S) (g : S ⟶ R) (f : T ⟶ R) (h : f = i ≫ g) :
    (leftDerivedUpperStarComp A i g).symm ≪≫
        eqToIso (congrArg (fun h : T ⟶ R ↦ L((h)^*[A])) h.symm) =
      (leftDerivedUpperStarCongr A h ≪≫ leftDerivedUpperStarComp A i g).symm := by
  subst h
  ext
  simp [leftDerivedUpperStarCongr_rfl]

omit [UpperStarPreservesFlat A] in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem actionTensor_compactification_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    leftDerivedUpperStarCompactificationIso A c =
      (leftDerivedUpperStarCongr A c.comm ≪≫ leftDerivedUpperStarComp A c.i c.g).symm :=
  actionTensor_compactification_eq_aux A c.i c.g f c.comm

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem actionTensor_general_comp_inverse {T S R : Scheme.{u}}
    (i : T ⟶ S) (g : S ⟶ R) (f : T ⟶ R) (h : f = i ≫ g)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology R) A)) :
    (leftDerivedUpperStarCongr A h ≪≫ leftDerivedUpperStarComp A i g).inv.app (K ⊗ M) ≫
        ((leftDerivedUpperStarTensorComparison A f).app K).app M =
      L((i)^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A i).app _).app _ ≫
        ((leftDerivedUpperStarCongr A h ≪≫ leftDerivedUpperStarComp A i g).inv.app K ⊗ₘ
          (leftDerivedUpperStarCongr A h ≪≫ leftDerivedUpperStarComp A i g).inv.app M) := by
  subst h
  have := actionTensor_underived_comp A i g
  have hc := CategoryTheory.Functor.generic_composite (g)^*[A] (i)^*[A]
    (i ≫ g)^*[A] (upperStarComp A i g) K M
  have ht := tensor_comparison_inverse L((g)^*[A]) L((i)^*[A]) L((i ≫ g)^*[A])
    (((i ≫ g)^*[A]).leftDerivedFunctorNatIso (upperStarComp A i g) ≪≫
      ((g)^*[A]).leftDerivedFunctorCompIso (i)^*[A])
    (fun K M ↦ (((g)^*[A]).leftDerivedTensorComparison.app K).app M)
    (fun K M ↦ (((i)^*[A]).leftDerivedTensorComparison.app K).app M)
    (fun K M ↦ (((i ≫ g)^*[A]).leftDerivedTensorComparison.app K).app M) K M hc
  simpa only [leftDerivedUpperStarCongr_rfl, Iso.refl_trans, leftDerivedUpperStarComp,
    actionTensor_comparison_eq, Category.assoc] using ht

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
private theorem actionTensor_compactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (K ⊗ M) ≫
        ((leftDerivedUpperStarTensorComparison A f).app K).app M =
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app K ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app M) := by
  rw [actionTensor_compactification_eq]
  exact actionTensor_general_comp_inverse A c.i c.g f c.comm K M

end ActionComposition

section ActionOpen

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open Functor.LaxMonoidal

private theorem actionTensor_mixed_component
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app M =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app K ▷ L((j)^*[A]).obj M ≫
        inv (((leftDerivedUpperStarTensorComparison A j).app K).app M) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app (K ⊗ M) := by
  have h : ((leftDerivedUpperStarTensorNatIso A j).inv.app K).app M =
      inv (((leftDerivedUpperStarTensorComparison A j).app K).app M) :=
    IsIso.eq_inv_of_hom_inv_id
      (f := ((leftDerivedUpperStarTensorComparison A j).app K).app M)
      (((leftDerivedUpperStarTensorNatIso A j).app K).app M).hom_inv_id
  rw [← h]
  rfl

/-- The comparison `j^*X ⊗ᴸ Lj^*M ≅ j^*(X ⊗ᴸ M)` is compatible with the monoidal structure of
`Lj^*`. -/
private theorem actionTensor_mixed_assoc
    (K M M' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (α_ (D((j)^*[A]).obj K) (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).hom ≫
        D((j)^*[A]).obj K ◁ inv (((leftDerivedUpperStarTensorComparison A j).app M).app M') ≫
          ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app (M ⊗ M') ≫
            D((j)^*[A]).map (α_ K M M').inv =
      ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app M ▷
          L((j)^*[A]).obj M' ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app (K ⊗ M)).app M' := by
  apply mixed_comparison_assoc L((j)^*[A]) D((j)^*[A])
    (leftDerivedUpperStarIsoMapDerivedCategory A j)
    (fun M N ↦ inv (((leftDerivedUpperStarTensorComparison A j).app M).app N))
    (fun K M N ↦ inverse_comparison_assoc L((j)^*[A])
      (fun K M ↦ asIso (((leftDerivedUpperStarTensorComparison A j).app K).app M))
      (actionTensor_assoc A j) K M N)
    (fun K M ↦ ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app M)
    (fun K M ↦ ?_) K M M'
  exact actionTensor_mixed_component A j _ _

/-- The projection map `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of an open immersion is compatible with the
associators. -/
private theorem actionTensor_open_assoc
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (M M' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    D((j)_!open[A]).map (α_ K (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).hom ≫
        D((j)_!open[A]).map (K ◁ inv (((leftDerivedUpperStarTensorComparison A j).app M).app M')) ≫
          ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (M ⊗ M') ≫
            (α_ (D((j)_!open[A]).obj K) M M').inv =
      ((derivedOpenImmersionLowerShriekProjectionMap A j).app (K ⊗ L((j)^*[A]).obj M)).app M' ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M ▷ M' :=
  projection_map_assoc_data (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    L((j)^*[A])
    (fun M N ↦ inv (((leftDerivedUpperStarTensorComparison A j).app M).app N))
    (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (actionTensor_mixed_assoc A j) K M M'

private theorem actionTensor_open_inverse_assoc
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) A))
    (N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N ▷ N' ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app
          (K ⊗ L((j)^*[A]).obj N)).app N' =
      (α_ _ _ _).hom ≫ ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app
          (N ⊗ N') ≫
        D((j)_!open[A]).map (K ◁ ((leftDerivedUpperStarTensorComparison A j).app N).app N' ≫
          (α_ _ _ _).inv) := by
  have h₀ := actionTensor_open_assoc A j K N N'
  have h := inverse_action_assoc D((j)_!open[A]) L((j)^*[A])
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A j).app N).app N')
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app N)
    K N N' h₀
  exact h

end ActionOpen

private theorem genericProjectionAction_open_counit
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
      (D((f)^*[A]).obj F)).app N) ≫
      D((f)_!open[A]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso A f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A
        f).counit.app (((derivedTensor A Y).obj F).obj N) =
    ((derivedTensor A Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A
      f).counit.app F)).app N := by
  exact projection_counit_iso (derivedOpenImmersionLowerShriekUpperStarAdjunction A f)
    L((f)^*[A]) (derivedTensor A X) (derivedTensor A Y)
    (mapDerivedCategoryUpperStarDerivedTensorIso A f).hom F N
    (((derivedOpenImmersionLowerShriekProjectionIso A f).app
      (D((f)^*[A]).obj F)).app N) rfl


private theorem genericProjectionAction_open
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (projectionActionAssociator A Y (D((f)_!open[A]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
        M).app (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      D((f)_!open[A]).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (projectionActionAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  simpa only [projectionActionAssociator, derivedTensor, leftDerivedUpperStarTensorIso_hom,
    curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj] using
    (actionTensor_open_inverse_assoc
      A f M N₁ N₂).symm

private theorem genericProjectionAction_proper
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (projectionActionAssociator A Y (R((f)_*[A]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap A f).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      R((f)_*[A]).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (projectionActionAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map (((rightDerivedLowerStarProjectionMap
      A f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap A f).app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  have h := (derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMap_associativity
    (leftDerivedUpperStarTensorComparison A f)
    (actionTensor_assoc A f) M N₁ N₂
  simpa only [Category.assoc] using cancel_iso_map R((f)_*[A])
    (projectionActionAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂))
    (((derivedTensor A Y).map (((rightDerivedLowerStarProjectionMap A f).app M).app N₁)).app N₂ ≫
      ((rightDerivedLowerStarProjectionMap A f).app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂)
    ((projectionActionAssociator A Y
      (R((f)_*[A]).obj M) N₁ N₂).hom ≫
      ((rightDerivedLowerStarProjectionMap A f).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂))
    (((derivedTensor A X).obj M).map (leftDerivedUpperStarTensorIso A f N₁ N₂).hom) (by
      simpa only [derivedTensor, projectionActionAssociator, leftDerivedUpperStarTensorIso_hom,
        curriedTensor_obj_obj, curriedTensor_obj_map, curriedTensor_map_app,
        rightDerivedLowerStarProjectionMap, Category.assoc] using h)


section ComparisonComponents
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

private theorem raw_comparison_tensor
    (N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (N ⊗ N') ≫
        ((leftDerivedUpperStarTensorComparison A f).app N).app N' =
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app N).app N') ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app N ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app N') := by
  exact actionTensor_compactification A c N N'

private theorem component_comparison_tensor
    (N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
        (leftDerivedUpperStarCompactificationIso A c) (N ⊗ N') ≫
      ((leftDerivedUpperStarTensorComparison A f).app N).app N' =
    L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app N).app N') ≫
      ((leftDerivedUpperStarTensorComparison A c.i).app (L((c.g)^*[A]).obj N)).app
        (L((c.g)^*[A]).obj N') ≫
      (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c) N ⊗ₘ
        compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c) N') := by
  exact compositionComponent_tensor L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
    (leftDerivedUpperStarCompactificationIso A c)
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app L).app L')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app L).app L')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A f).app L).app L')
    (raw_comparison_tensor A c) N N'

end ComparisonComponents

section ActionCertificates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

omit [UpperStarPreservesFlat A] in
private theorem actionTensor_functor_eq (X : Scheme.{u}) :
    derivedTensor A X = curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) := by
  rfl

omit [UpperStarPreservesFlat A] in
private theorem actionTensor_associator_heq (X : Scheme.{u}) :
    HEq (projectionActionAssociator A X)
      (fun K M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ↦ α_ K M N) := by
  rfl

private theorem actionTensor_pullback_heq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (fun N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ↦
      (leftDerivedUpperStarTensorIso A f N N').hom)
      (fun N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ↦
        ((leftDerivedUpperStarTensorComparison A f).app N).app N') := by
  rfl

end ActionCertificates

private theorem compactificationComponent_eq
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((projectionMapOfCompactification A c).app M).app N =
      composite_projection_bifunctor (derivedTensor A X) (derivedTensor A Y)
        (derivedTensor A c.Z)
        (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
        R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
        (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c)) M N := by
  simpa only [composite_projection_bifunctor, compositionComponent] using
    projectionMapOfCompactification_app_app A c M N

private theorem genericProjectionAction_compactification
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (projectionActionAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification A c).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (projectionActionAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map (((projectionMapOfCompactification
      A c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification A c).app (((derivedTensor
        A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  have h := composite_projection_bifunctor_action
    (derivedTensor A X) (derivedTensor A Y) (derivedTensor A c.Z)
    (actionTensor_functor_eq A X) (actionTensor_functor_eq A Y)
    (actionTensor_functor_eq A c.Z)
    (projectionActionAssociator A X) (projectionActionAssociator A Y)
    (projectionActionAssociator A c.Z)
    (actionTensor_associator_heq A X) (actionTensor_associator_heq A Y)
    (actionTensor_associator_heq A c.Z)
    (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
    R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
    (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
    (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
      (leftDerivedUpperStarCompactificationIso A c))
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A c.g N N').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A c.i N N').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom)
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app N).app N')
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app N).app N')
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A f).app N).app N')
    (actionTensor_pullback_heq A c.g) (actionTensor_pullback_heq A c.i)
    (actionTensor_pullback_heq A f)
    (fun x N ↦ congr_app ((rightDerivedLowerStarProjectionMap A c.g).naturality x) N)
    (genericProjectionAction_proper A c.g)
    (fun x N ↦ congr_app
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.naturality x) N)
    (fun K _ _ x ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).naturality x)
    (fun K N N' ↦ (genericProjectionAction_open A c.i K N N').symm)
    (component_comparison_tensor A c) M N₁ N₂
  rw [compactificationComponent_eq A f c M (((derivedTensor A Y).obj N₁).obj N₂),
    compactificationComponent_eq A f c M N₁,
    compactificationComponent_eq A f c (((derivedTensor A X).obj M).obj
      (L((f)^*[A]).obj N₁)) N₂]
  exact h

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Proper projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_proper (ModuleCat.{u + 1} P.Coefficient) f M N₁ N₂


/-- Open projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_open
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (D((f)_!open[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        M).app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_open (ModuleCat.{u + 1} P.Coefficient) f M N₁ N₂


/-- Chosen-compactification projection tensor action, with reassociation and the canonical pullback
  tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_compactification
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app (((derivedTensor
        (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_compactification
    (ModuleCat.{u + 1} P.Coefficient) f c M N₁ N₂


/-- Open-counit tensor compatibility, using the mixed exact/derived restriction
comparison to display the canonical identification of exact inverse image with Lf*.
Source: blueprint expanded Step 6, Stacks Tags 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: Cancel the invertible open tensor map. Transpose through the open adjunction.
The left side transposes to the inverse restriction/tensor comparison. The inverse
open tensor normalization makes the right transpose the same comparison followed
by restriction of the counit tensor identity and the unit tensor identity. The
triangle identity cancels those last two maps. Injectivity of the adjunction
bijection gives equality; recompose with the open tensor isomorphism. The same
argument on each site uses its exact degreewise unit and counit, for unbounded
complexes, without assuming that any proper projection map is invertible. -/
theorem finiteProjectionAction_open_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      (D((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj F)).app N) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        f).counit.app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj F).obj N) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      f).counit.app F)).app N := by
  exact genericProjectionAction_open_counit (ModuleCat.{u + 1} P.Coefficient) f F N

end AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.Etale

attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

private theorem genericProjectionAction_open_counit
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {X Y : Scheme.{u}}
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (f : X ⟶ Y) [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
      (D((f)^*[A]).obj F)).app N) ≫
      D((f)_!open[A]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso A f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A
        f).counit.app (((derivedTensor A Y).obj F).obj N) =
    ((derivedTensor A Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A
      f).counit.app F)).app N := by
  exact projection_counit_iso (derivedOpenImmersionLowerShriekUpperStarAdjunction A f)
    L((f)^*[A]) (derivedTensor A X) (derivedTensor A Y)
    (mapDerivedCategoryUpperStarDerivedTensorIso A f).hom F N
    (((derivedOpenImmersionLowerShriekProjectionIso A f).app
      (D((f)^*[A]).obj F)).app N) rfl


private theorem genericProjectionAction_proper
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorAssociator A Y (R((f)_*[A]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap A f).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      R((f)_*[A]).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (derivedTensorAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map (((rightDerivedLowerStarProjectionMap
      A f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap A f).app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  have h := (derivedUpperStarLowerStarAdjunction A f).rightAdjointProjectionMap_associativity
    (leftDerivedUpperStarTensorComparison A f)
    (leftDerivedUpperStarTensorComparison_associativity A f) M N₁ N₂
  simpa only [Category.assoc] using cancel_iso_map R((f)_*[A])
    (derivedTensorAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂))
    (((derivedTensor A Y).map (((rightDerivedLowerStarProjectionMap A f).app M).app N₁)).app N₂ ≫
      ((rightDerivedLowerStarProjectionMap A f).app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂)
    ((derivedTensorAssociator A Y
      (R((f)_*[A]).obj M) N₁ N₂).hom ≫
      ((rightDerivedLowerStarProjectionMap A f).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂))
    (((derivedTensor A X).obj M).map (leftDerivedUpperStarTensorIso A f N₁ N₂).hom) (by
      simpa only [derivedTensor, derivedTensorAssociator, leftDerivedUpperStarTensorIso_hom,
        curriedTensor_obj_obj, curriedTensor_obj_map, curriedTensor_map_app,
        rightDerivedLowerStarProjectionMap, Category.assoc] using h)


private theorem genericProjectionAction_open
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (f : X ⟶ Y) [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorAssociator A Y (D((f)_!open[A]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
        M).app (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      D((f)_!open[A]).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (derivedTensorAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso A f).inv.app
        (((derivedTensor A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  simpa only [derivedTensorAssociator, derivedTensor, leftDerivedUpperStarTensorIso_hom,
    curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj] using
    (derivedOpenImmersionLowerShriekProjectionIso_inv_associativity
      A f M N₁ N₂).symm


section ComparisonComponents
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

private theorem raw_comparison_tensor
    (N N' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (N ⊗ N') ≫
        ((leftDerivedUpperStarTensorComparison A f).app N).app N' =
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app N).app N') ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app N ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app N') := by
  exact leftDerivedUpperStarCompactificationIso_hom_app_tensor A c N N'

private theorem component_comparison_tensor
    (N N' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
        (leftDerivedUpperStarCompactificationIso A c) (N ⊗ N') ≫
      ((leftDerivedUpperStarTensorComparison A f).app N).app N' =
    L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app N).app N') ≫
      ((leftDerivedUpperStarTensorComparison A c.i).app (L((c.g)^*[A]).obj N)).app
        (L((c.g)^*[A]).obj N') ≫
      (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c) N ⊗ₘ
        compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c) N') := by
  exact compositionComponent_tensor L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
    (leftDerivedUpperStarCompactificationIso A c)
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app L).app L')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app L).app L')
    (fun L L' ↦ ((leftDerivedUpperStarTensorComparison A f).app L).app L')
    (raw_comparison_tensor A c) N N'

end ComparisonComponents

section ActionCertificates
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

omit [UpperStarPreservesFlat A] in
private theorem actionTensor_functor_eq (X : Scheme.{u}) :
    derivedTensor A X = curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A)) := by
  rfl

omit [UpperStarPreservesFlat A] in
private theorem actionTensor_associator_heq (X : Scheme.{u}) :
    HEq (derivedTensorAssociator A X)
      (fun K M N : DerivedCategory (Sheaf X.smallEtaleTopology A) ↦ α_ K M N) := by
  rfl

private theorem actionTensor_pullback_heq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (fun N N' : DerivedCategory (Sheaf Y.smallEtaleTopology A) ↦
      (leftDerivedUpperStarTensorIso A f N N').hom)
      (fun N N' : DerivedCategory (Sheaf Y.smallEtaleTopology A) ↦
        ((leftDerivedUpperStarTensorComparison A f).app N).app N') := by
  rfl

end ActionCertificates

private theorem compactificationComponent_eq
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app M).app N =
      composite_projection_bifunctor (derivedTensor A X) (derivedTensor A Y)
        (derivedTensor A c.Z)
        (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
        R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
        (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
        (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
        (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
          (leftDerivedUpperStarCompactificationIso A c)) M N := by
  simpa only [composite_projection_bifunctor, compositionComponent] using
    projectionMapOfCompactification_app_app A c M N

private theorem genericProjectionAction_compactification
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedTensorAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification A c).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (derivedTensorAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map (((projectionMapOfCompactification
      A c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification A c).app (((derivedTensor
        A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂) := by
  have h := composite_projection_bifunctor_action
    (derivedTensor A X) (derivedTensor A Y) (derivedTensor A c.Z)
    (actionTensor_functor_eq A X) (actionTensor_functor_eq A Y)
    (actionTensor_functor_eq A c.Z)
    (derivedTensorAssociator A X) (derivedTensorAssociator A Y)
    (derivedTensorAssociator A c.Z)
    (actionTensor_associator_heq A X) (actionTensor_associator_heq A Y)
    (actionTensor_associator_heq A c.Z)
    (F' := L((c.i)^*[A])) (F'' := L((f)^*[A]))
    R((c.g)_*[A]) D((c.i)_!open[A]) L((c.g)^*[A])
    (fun K N ↦ ((rightDerivedLowerStarProjectionMap A c.g).app K).app N)
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
    (compositionComponent L((c.g)^*[A]) L((c.i)^*[A]) L((f)^*[A])
      (leftDerivedUpperStarCompactificationIso A c))
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A c.g N N').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A c.i N N').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso A f N N').hom)
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app N).app N')
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app N).app N')
    (fun N N' ↦ ((leftDerivedUpperStarTensorComparison A f).app N).app N')
    (actionTensor_pullback_heq A c.g) (actionTensor_pullback_heq A c.i)
    (actionTensor_pullback_heq A f)
    (fun x N ↦ congr_app ((rightDerivedLowerStarProjectionMap A c.g).naturality x) N)
    (genericProjectionAction_proper A c.g)
    (fun x N ↦ congr_app
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.naturality x) N)
    (fun K _ _ x ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).naturality x)
    (fun K N N' ↦ (genericProjectionAction_open A c.i K N N').symm)
    (component_comparison_tensor A c) M N₁ N₂
  rw [compactificationComponent_eq A f c M (((derivedTensor A Y).obj N₁).obj N₂),
    compactificationComponent_eq A f c M N₁,
    compactificationComponent_eq A f c (((derivedTensor A X).obj M).obj
      (L((f)^*[A]).obj N₁)) N₂]
  exact h

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- Proper projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_proper (ModuleCat.{u + 1} P.Coefficient) f M N₁ N₂


/-- Open projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_open
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y (D((f)_!open[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        M).app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_open (ModuleCat.{u + 1} P.Coefficient) f M N₁ N₂


/-- Chosen-compactification projection tensor action, with reassociation and the canonical pullback
  tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_compactification
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app (((derivedTensor
        (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  exact genericProjectionAction_compactification
    (ModuleCat.{u + 1} P.Coefficient) f c M N₁ N₂


/-- Open-counit tensor compatibility, using the mixed exact/derived restriction
comparison to display the canonical identification of exact inverse image with Lf*.
Source: blueprint expanded Step 6, Stacks Tags 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: Cancel the invertible open tensor map. Transpose through the open adjunction.
The left side transposes to the inverse restriction/tensor comparison. The inverse
open tensor normalization makes the right transpose the same comparison followed
by restriction of the counit tensor identity and the unit tensor identity. The
triangle identity cancels those last two maps. Injectivity of the adjunction
bijection gives equality; recompose with the open tensor isomorphism. The same
argument on each site uses its exact degreewise unit and counit, for unbounded
complexes, without assuming that any proper projection map is invertible. -/
theorem finiteProjectionAction_open_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      (D((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj F)).app N) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        f).counit.app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj F).obj N) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      f).counit.app F)).app N := by
  exact genericProjectionAction_open_counit (ModuleCat.{u + 1} P.Coefficient) f F N

end AlgebraicGeometry.Etale
