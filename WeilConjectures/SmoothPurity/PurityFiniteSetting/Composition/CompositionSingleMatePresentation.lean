/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteCounitProjectionTransport
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-! # Purity in the standing tensor-mate coordinates -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale.CompositionTensorMate

section ProofHelpers

-- Serialize concrete comparisons to bound simultaneous conversion checking.
set_option Elab.async false

set_option cleanup.letToHave false
set_option linter.style.multiGoal false

-- Use the sheaf abelian data cached by the generic six-functor constructions.
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
attribute [local instance 2000] isNoetherian_of_finite
-- Match the coefficient braiding used by the generic derived constructions.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory ProEtale.sheafBraidedCategory

private theorem transport_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {L V : C ⥤ D} (e : L ≅ V)
    (δ : ∀ A B, L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B)
    (hδ : ∀ A B, L.map (β_ A B).hom ≫ δ B A =
      δ A B ≫ (β_ (L.obj A) (L.obj B)).hom) (A B : C) :
    V.map (β_ A B).hom ≫ e.inv.app (B ⊗ A) ≫ δ B A ≫
        (e.hom.app B ⊗ₘ e.hom.app A) =
      e.inv.app (A ⊗ B) ≫ δ A B ≫ (e.hom.app A ⊗ₘ e.hom.app B) ≫
        (β_ (V.obj A) (V.obj B)).hom := by
  rw [e.inv.naturality_assoc, reassoc_of% hδ A B]
  rw [BraidedCategory.braiding_naturality]

private theorem tensor_source_calculation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (V : C ⥤ D) {N O U : C} {A W B Z : D}
    (p : A ⟶ V.obj N) (v : W ⟶ V.obj O) (c : V.obj N ⟶ B)
    (r : V.obj U ⟶ Z) (a : O ⟶ U)
    (tNO : V.obj (N ⊗ O) ≅ V.obj N ⊗ V.obj O)
    (tNU : V.obj (N ⊗ U) ≅ V.obj N ⊗ V.obj U)
    (tUN : V.obj (U ⊗ N) ≅ V.obj U ⊗ V.obj N)
    (hn : V.map (N ◁ a) ≫ tNU.hom = tNO.hom ≫ V.obj N ◁ V.map a)
    (hb : V.map (β_ N U).hom ≫ tUN.hom =
      tNU.hom ≫ (β_ (V.obj N) (V.obj U)).hom)
    (hs : (β_ B Z).hom ≫ (β_ Z B).hom = 𝟙 _) :
    (p ⊗ₘ v) ≫ tNO.inv ≫ V.map (N ◁ a) ≫ V.map (β_ N U).hom ≫
        tUN.hom ≫ (r ⊗ₘ c) ≫ (β_ Z B).hom =
      (p ≫ c) ⊗ₘ (v ≫ V.map a ≫ r) := by
  have hn' : tNO.inv ≫ V.map (N ◁ a) = V.obj N ◁ V.map a ≫ tNU.inv := by
    apply (cancel_mono tNU.hom).1
    simp only [Category.assoc, hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hb' : tNU.inv ≫ V.map (β_ N U).hom ≫ tUN.hom =
      (β_ (V.obj N) (V.obj U)).hom := by
    rw [hb, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn']
  rw [reassoc_of% hb']
  rw [← reassoc_of% (BraidedCategory.braiding_naturality c r)]
  simp only [hs, Category.comp_id]
  rw [← id_tensorHom]
  simp only [tensorHom_comp_tensorHom, Category.id_comp]

private theorem inverse_square
    {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ B) (b : U ≅ V) (p : A ⟶ U) (q : B ⟶ V)
    [IsIso p] (h : a.hom ≫ q = p ≫ b.hom) : IsIso q := by
  have hq : q = a.inv ≫ p ≫ b.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [hq]
  infer_instance

private theorem inverse_square_eq
    {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ B) (b : U ≅ V) (p : A ⟶ U) (q : B ⟶ V)
    [IsIso p] [IsIso q] (h : a.hom ≫ q = p ≫ b.hom) :
    b.hom ≫ inv q = inv p ≫ a.hom := by
  apply (cancel_epi p).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem invert_projection_square
    {C : Type*} [Category C] {A B Q S T U : C}
    (p : A ⟶ B) (q : U ⟶ S) [IsIso p] [IsIso q]
    (b : Q ≅ B) (i : Q ≅ S) (t : A ≅ T) (w : T ≅ U)
    (h : p ≫ b.inv ≫ i.hom = t.hom ≫ w.hom ≫ q) :
    i.hom ≫ inv q = b.hom ≫ inv p ≫ t.hom ≫ w.hom := by
  have h' := congrArg (fun z ↦ b.hom ≫ inv p ≫ z ≫ inv q) h
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    IsIso.hom_inv_id, Category.comp_id] using h'

private theorem projection_tail_calculation
    {C : Type*} [Category C] {P Q R S T U V W X Y : C}
    (c : P ⟶ Q) (b : Q ⟶ R) (qi : R ⟶ S) (pi : Q ⟶ T)
    (a : T ⟶ S) (ε : S ⟶ U) (l : U ⟶ V)
    (i : P ⟶ W) (vi : W ⟶ X) (t : X ⟶ Y) (w : Y ⟶ T) (z : X ⟶ V)
    (h₁ : b ≫ qi = pi ≫ a) (h₂ : c ≫ pi = i ≫ vi ≫ t ≫ w)
    (h₃ : t ≫ w ≫ a ≫ ε ≫ l = z) :
    c ≫ b ≫ qi ≫ ε ≫ l = i ≫ vi ≫ z := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem transport_tensor_hom
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L V : C ⥤ D} (e : L ≅ V)
    (δ : ∀ J, (curriedTensor C).obj J ⋙ L ≅ L ⋙ (curriedTensor D).obj (L.obj J))
    (J K : C) :
    ((Functor.isoWhiskerLeft _ e.symm ≪≫ δ J ≪≫
      Functor.isoWhiskerRight e _ ≪≫
      Functor.isoWhiskerLeft V ((curriedTensor D).mapIso (e.app J))).hom.app K) =
      e.inv.app (J ⊗ K) ≫ (δ J).hom.app K ≫
        (e.hom.app J ⊗ₘ e.hom.app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    curriedTensor_obj_map, curriedTensor_map_app, curriedTensor_obj_obj,
    MonoidalCategory.tensorHom_def']

section DerivedComparison

universe v v₁ v₂

variable {C : Type v₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type v₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private theorem derived_comparison_tensor (J K : _root_.DerivedCategory C) :
    ((Functor.isoWhiskerLeft _ F.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (asIso F.leftDerivedTensorComparison).app J ≪≫
      Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory ((curriedTensor _).mapIso
        (F.leftDerivedFunctorIsoMapDerivedCategory.app J))).hom.app K) =
      (F.mapDerivedCategoryTensorComparison.app J).app K := by
  exact (transport_tensor_hom F.leftDerivedFunctorIsoMapDerivedCategory
    (fun J ↦ (asIso F.leftDerivedTensorComparison).app J) J K).trans
      (F.mapDerivedCategoryTensorComparison_app_app J K).symm

private theorem derived_comparison_braiding
    (hF : ∀ J K, F.map (β_ J K).hom ≫ Functor.OplaxMonoidal.δ F K J =
      Functor.OplaxMonoidal.δ F J K ≫ (β_ (F.obj J) (F.obj K)).hom)
    (J K : _root_.DerivedCategory C) :
    letI := _root_.DerivedCategory.braidedCategory' C
    letI := _root_.DerivedCategory.braidedCategory' D
    F.mapDerivedCategory.map (β_ J K).hom ≫
        (F.mapDerivedCategoryTensorComparison.app K).app J =
      (F.mapDerivedCategoryTensorComparison.app J).app K ≫
        (β_ (F.mapDerivedCategory.obj J) (F.mapDerivedCategory.obj K)).hom := by
  let := _root_.DerivedCategory.braidedCategory' C
  let := _root_.DerivedCategory.braidedCategory' D
  have ht := transport_braiding F.leftDerivedFunctorIsoMapDerivedCategory
    (fun J K ↦ (F.leftDerivedTensorComparison.app J).app K)
    (fun J K ↦ F.leftDerivedFunctor_map_braiding_hom_δ hF J K) J K
  simpa only [Functor.mapDerivedCategoryTensorComparison_app_app, Category.assoc] using ht

private theorem derived_comparison_koszul
    (hF : ∀ J K, F.map (β_ J K).hom ≫ Functor.OplaxMonoidal.δ F K J =
      Functor.OplaxMonoidal.δ F J K ≫ (β_ (F.obj J) (F.obj K)).hom)
    (J K : _root_.DerivedCategory C) :
    F.mapDerivedCategory.map (derivedTensorKoszulSymmetry C J K).hom ≫
        (F.mapDerivedCategoryTensorComparison.app K).app J =
      (F.mapDerivedCategoryTensorComparison.app J).app K ≫
        (derivedTensorKoszulSymmetry D
          (F.mapDerivedCategory.obj J) (F.mapDerivedCategory.obj K)).hom := by
  have h := derived_comparison_braiding F hF J K
  simpa only [derivedTensorKoszulSymmetry, BraidedCategory.braiding,
    _root_.DerivedCategory.braidedCategory', DerivedMonoidal.braidedCategory'] using h

end DerivedComparison

-- Normalize proof-local transport data before checking concrete derived categories.
local syntax (name := startMateProof) "start_mate_proof" : tactic
local syntax (name := finishMateProof) "finish_mate_proof" : tactic

open Lean Meta Elab Tactic in
@[local tactic startMateProof] private meta def elabStartMateProof : Tactic := fun _ => do
  withMainContext do
    let g ← getMainGoal
    let h ← mkFreshExprSyntheticOpaqueMVar (← g.getType)
    g.setTag h.mvarId!.name
    replaceMainGoal [h.mvarId!, g]

open Lean Meta Elab Tactic in
@[local tactic finishMateProof] private meta def elabFinishMateProof : Tactic := fun _ => do
  withMainContext do
    let g ← getMainGoal
    let h : MVarId := ⟨← g.getTag⟩
    let proof ← instantiateMVars (mkMVar h)
    if proof.hasMVar then
      throwError "The mate proof has unresolved goals"
    let helpers := #[``transport_tensor_hom, ``transport_braiding,
      ``derived_comparison_tensor, ``derived_comparison_koszul, ``derived_comparison_braiding,
      ``tensor_source_calculation, ``projection_tail_calculation,
      ``inverse_square, ``inverse_square_eq,
      ``invert_projection_square]
    let proof ← Meta.transform proof (skipConstInApp := true) (pre := fun e => do
      if let .const n us := e.getAppFn then
        if helpers.contains n then
          let ci ← getConstInfo n
          return .visit ((← instantiateValueLevelParams ci us (allowOpaque := true)).beta
            e.getAppArgs)
      return .continue)
    let proof ← zetaReduce proof
    if proof.hasSorry then
      throwError "The mate proof contains an unfinished proof"
    g.assign proof
    replaceMainGoal []

attribute [local irreducible] Functor.rightAdjoint Adjunction.ofIsLeftAdjoint

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  start_mate_proof
  · refine ⟨h.1, ?_⟩
    intro M N he f hf hN F i hi
    exact h.2 M N (he.map (fun eM ↦ eM ≪≫ e.symm)) f hf hN F i hi
  · finish_mate_proof

private theorem dualizing_boundedConstructible
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    Etale.DerivedCategory.isBoundedConstructible P.Coefficient X
      (Etale.dualizingComplex P.Coefficient f) := by
  start_mate_proof
  · let := P.finiteComparedInvertibleExponent aY
    have hu : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} P.Coefficient) Y (𝟙_ _) := by
      exact ⟨(Etale.DerivedCategory.boundedConstructible _ Y).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
        0, 0, (Etale.DerivedCategory.torAmplitudeIn _ Y 0 0).prop_of_iso
          (_root_.DerivedCategory.singleFunctorObjUnitIso _)
          (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
            (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
    have h := (Etale.constructibleFiniteTor_dualizingComplex P.Coefficient aY f hu).1
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (h.2 i), ?_⟩
    obtain ⟨a, ha⟩ := h.1.1
    obtain ⟨b, hb⟩ := h.1.2
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ha i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp hb i (lt_of_le_of_lt (le_max_right _ _) hi)
  · finish_mate_proof

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification ProEtale.projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap ProEtale.rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso
  ProEtale.derivedOpenImmersionLowerShriekProjectionIso

end ProofHelpers

variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

end WeilConjectures.PurityFiniteSetting
