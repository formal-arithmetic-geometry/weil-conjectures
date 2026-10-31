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

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale.CompositionTensorMate

/-- Change from the inverse-shift presentation to the left-derived tensor source.
Source: composition proof Step 2, twist reassociation and exact pullback comparison
(blueprint: lem-route-composition-single-mate-presentation). -/
def compositionMateSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.compositionShiftedPullback f d).obj K ≅
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
        ((S P.Coefficient f).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) ⊗
            P.diagonalTwist X d) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    (P.smoothPurityReassociation X d ((P.smoothPurityPullback f).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)) ≪≫
    compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).symm.app
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))
      (Iso.refl (P.diagonalTwist X d)))

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

private theorem adjunction_delta_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [iG : G.LaxMonoidal] (adj : F ⊣ G)
    (hG : ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
    (X Y : C) :
    letI := adj.leftAdjointOplaxMonoidal
    F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  let : G.LaxBraided := { toLaxMonoidal := iG, braided := hG }
  exact (Adjunction.leftAdjointOplaxMonoidal_δ_braiding adj X Y).symm

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

private theorem canonical_symmetry_hom (J K : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app J).app K =
      (derivedTensorKoszulSymmetry C J K).hom := by
  rfl

private theorem derived_tensor_source_calculation
    (V : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    {N O U : _root_.DerivedCategory C} {A W B Z : _root_.DerivedCategory D}
    (p : A ⟶ V.obj N) (v : W ⟶ V.obj O) (c : V.obj N ⟶ B)
    (r : V.obj U ⟶ Z) (a : O ⟶ U)
    (tNO : V.obj (N ⊗ O) ≅ V.obj N ⊗ V.obj O)
    (tNU : V.obj (N ⊗ U) ≅ V.obj N ⊗ V.obj U)
    (tUN : V.obj (U ⊗ N) ≅ V.obj U ⊗ V.obj N)
    (hn : V.map (N ◁ a) ≫ tNU.hom = tNO.hom ≫ V.obj N ◁ V.map a)
    (hb : V.map (derivedTensorKoszulSymmetry C N U).hom ≫ tUN.hom =
      tNU.hom ≫ (derivedTensorKoszulSymmetry D (V.obj N) (V.obj U)).hom)
    (hs : (derivedTensorKoszulSymmetry D B Z).hom ≫
      (derivedTensorKoszulSymmetry D Z B).hom = 𝟙 _) :
    (p ⊗ₘ v) ≫ tNO.inv ≫ V.map (N ◁ a) ≫
        V.map (derivedTensorKoszulSymmetry C N U).hom ≫
        tUN.hom ≫ (r ⊗ₘ c) ≫ (derivedTensorKoszulSymmetry D Z B).hom =
      (p ≫ c) ⊗ₘ (v ≫ V.map a ≫ r) := by
  let bC := _root_.DerivedCategory.braidedCategory' C
  let bD := _root_.DerivedCategory.braidedCategory' D
  have h := tensor_source_calculation V p v c r a tNO tNU tUN hn hb hs
  simpa only [bC, bD, derivedTensorKoszulSymmetry, BraidedCategory.braiding,
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

private theorem comparison_tensor_eq
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A J).hom.app K =
      (((ProEtale.comparisonUpperStar A X).mapDerivedCategoryTensorComparison).app J).app K := by
  start_mate_proof
  · exact derived_comparison_tensor (ProEtale.comparisonUpperStar A X) J K
  · finish_mate_proof

private theorem comparison_underived_braiding
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (J K : Sheaf X.smallEtaleTopology A) :
    (ProEtale.comparisonUpperStar A X).map (β_ J K).hom ≫
        Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar A X) K J =
      Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar A X) J K ≫
        (β_ ((ProEtale.comparisonUpperStar A X).obj J)
          ((ProEtale.comparisonUpperStar A X).obj K)).hom := by
  have hb (U V : Sheaf (Scheme.ProEt.topology X) A) :
      Functor.LaxMonoidal.μ (ProEtale.comparisonLowerStar A X) U V ≫
          (ProEtale.comparisonLowerStar A X).map (β_ U V).hom =
        (β_ ((ProEtale.comparisonLowerStar A X).obj U)
          ((ProEtale.comparisonLowerStar A X).obj V)).hom ≫
          Functor.LaxMonoidal.μ (ProEtale.comparisonLowerStar A X) V U := by
    let : (ProEtale.comparisonLowerStar A X).LaxBraided := by
      dsimp only [ProEtale.comparisonLowerStar]
      infer_instance
    exact Functor.LaxBraided.braided U V
  exact adjunction_delta_braiding (ProEtale.comparisonAdjunction A X) hb J K

private theorem comparison_braiding
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory.map
        (derivedTensorKoszulSymmetry
          (Sheaf X.smallEtaleTopology A) J K).hom ≫
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A K).hom.app J =
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A J).hom.app K ≫
      (derivedTensorKoszulSymmetry
        (Sheaf (Scheme.ProEt.topology X) A)
        ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj J)
        ((ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj K)).hom := by
  start_mate_proof
  · rw [comparison_tensor_eq, comparison_tensor_eq]
    exact derived_comparison_koszul (ProEtale.comparisonUpperStar A X)
      (comparison_underived_braiding A X) J K
  · finish_mate_proof

private theorem proEtale_derived_symmetry
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (J K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A) J K).hom ≫
      (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A) K J).hom = 𝟙 _ := by
  exact _root_.DerivedCategory.braiding_hom_braiding_hom
    (Sheaf (Scheme.ProEt.topology X) A) (fun _ _ ↦ SymmetricCategory.symmetry _ _) J K

private theorem comparison_factors_eq
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    let C := ProEtale.comparisonUpperStar A X
    C.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      C.mapDerivedCategoryFactors.hom.app K := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    change C.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      C.mapDerivedCategoryFactors.hom.app K
    erw [C.mapDerivedCategoryFactorsh_hom_app]
    have h₁ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology A)).hom.app K = 𝟙 _ := fun _ ↦ rfl
    have h₂ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).inv.app K = 𝟙 _ :=
      fun _ ↦ rfl
    have h₃ : ∀ K, (C.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := fun _ ↦ rfl
    erw [h₁, h₂, h₃, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  · finish_mate_proof

private theorem comparison_Qh_map
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    {K L : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ}
    (g : K ⟶ L) :
    _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map g) =
      _root_.DerivedCategory.Q.map g := by
  start_mate_proof
  · have h := _root_.DerivedCategory.quotientCompQhIso_hom_naturality g
    have hi : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).hom.app K = 𝟙 _ :=
      fun _ ↦ rfl
    rw [hi, hi] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  · finish_mate_proof

private theorem comparison_oplax_unit_formula
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat] :
    let C := ProEtale.comparisonUpperStar A X
    letI := C.mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η C.mapDerivedCategory =
      C.mapDerivedCategory.map
          (_root_.DerivedCategory.singleFunctorObjUnitIso
            (Sheaf X.smallEtaleTopology A)).inv ≫
        (C.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
        (_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) A) 0).map
          (Functor.OplaxMonoidal.η C) ≫
        (_root_.DerivedCategory.singleFunctorObjUnitIso
          (Sheaf (Scheme.ProEt.topology X) A)).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    let := C.mapDerivedCategoryOplaxMonoidal
    have h₁ : Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology
          A)) = 𝟙 _ := rfl
    have h₂ : Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X)
          A)) = 𝟙 _ := rfl
    change _ ≫ _ ≫ _ ≫ inv (Functor.LaxMonoidal.ε _) = _
    have hi : inv (Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X)
          A))) = 𝟙 _ := by
      apply (cancel_epi (Functor.LaxMonoidal.ε _)).1
      rw [IsIso.hom_inv_id, Category.comp_id]
      exact h₂.symm
    rw [h₁, CategoryTheory.Functor.map_id, Category.id_comp, hi, Category.comp_id,
      C.mapHomotopyCategory_η]
    have hq₁ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology A)).hom.app K = 𝟙 _ := fun _ ↦ rfl
    have hq₂ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).inv.app K = 𝟙 _ :=
      fun _ ↦ rfl
    have he₁ : (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology A) (.up ℤ))).hom = 𝟙 _ := rfl
    have he₂ : (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))).inv = 𝟙 _ := rfl
    simp only [_root_.DerivedCategory.singleFunctorObjUnitIso,
      Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, _root_.DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, asIso_hom, asIso_inv,
      h₁, hi, hq₁, hq₂, he₁, he₂, Functor.associator_hom_app,
      Functor.associator_inv_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    erw [comparison_factors_eq A X, comparison_Qh_map A X]
    simp only [Functor.mapCochainComplex_η, Functor.mapCochainComplexεIso,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Functor.Monoidal.εIso_inv, Functor.map_comp,
      Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    rfl
  · finish_mate_proof

private def derivedComparisonUnitIso
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (e : (ProEtale.comparisonUpperStar A X).obj (𝟙_ _) ≅ 𝟙_ _) :
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (ProEtale.comparisonUpperStar A X).mapDerivedCategory.mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ProEtale.comparisonUpperStar A X).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

private theorem comparison_oplax_unit_iso
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (e : (ProEtale.comparisonUpperStar A X).obj (𝟙_ _) ≅ 𝟙_ _)
    (hη : Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar A X) = e.hom) :
    letI := (ProEtale.comparisonUpperStar A X).mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar A X).mapDerivedCategory =
      (derivedComparisonUnitIso A X e).hom := by
  simpa only [derivedComparisonUnitIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, hη] using comparison_oplax_unit_formula A X

private theorem comparison_underived_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) =
      (ProEtale.comparisonUpperStarUnitIso A X).hom := by
  simp only [ProEtale.comparisonUpperStarUnitIso, asIso_hom]
  rfl

private theorem comparison_oplax_unit
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
    letI := C.mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η C.mapDerivedCategory =
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X).hom := by
  exact comparison_oplax_unit_iso (ModuleCat.{u + 1} A) X
    (ProEtale.comparisonUpperStarUnitIso A X) (comparison_underived_unit A X)

private theorem comparison_left_unitor_oplax
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let C := ProEtale.comparisonUpperStar A X
    letI := C.mapDerivedCategoryOplaxMonoidal
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A (𝟙_ _)).hom.app J ≫
      Functor.OplaxMonoidal.η C.mapDerivedCategory ▷ C.mapDerivedCategory.obj J ≫
      (λ_ (C.mapDerivedCategory.obj J)).hom = C.mapDerivedCategory.map (λ_ J).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    let := C.mapDerivedCategoryOplaxMonoidal
    rw [comparison_tensor_eq]
    simpa only [Functor.mapDerivedCategoryOplaxMonoidal_δ] using
      Functor.OplaxMonoidal.left_unitality_hom C.mapDerivedCategory J
  · finish_mate_proof

private theorem comparison_left_unitor
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (J : Etale.DerivedCategoryModule A X) :
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J ≫
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X).hom ▷
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J ≫
      (λ_ ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J)).hom =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (λ_ J).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
    let := C.mapDerivedCategoryOplaxMonoidal
    have h := comparison_left_unitor_oplax (ModuleCat.{u + 1} A) X J
    change (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J ≫
        Functor.OplaxMonoidal.η C.mapDerivedCategory ▷ C.mapDerivedCategory.obj J ≫
        (λ_ (C.mapDerivedCategory.obj J)).hom = C.mapDerivedCategory.map (λ_ J).hom at h
    erw [comparison_oplax_unit A X] at h
    exact h
  · finish_mate_proof


private theorem comparisonPullback_eq
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.sfComparisonPullbackIso A f =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm := by
  start_mate_proof
  · rfl
  · finish_mate_proof

private theorem sf_pullback_cancel
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y) :
    (ProEtale.sfDerivedComparisonPullbackIso A f).hom.app J ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).inv.app J) ≫
      (ProEtale.comparisonOpenDerivedPullbackIso (ULift.{u + 1} A) f).hom.app J =
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory.obj J) := by
  start_mate_proof
  · simp only [ProEtale.sfDerivedComparisonPullbackIso, comparisonPullback_eq,
      ProEtale.comparisonOpenDerivedPullbackIso, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
      Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc]
  · finish_mate_proof

private theorem smoothPullbackComparison_eq
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : D P.Coefficient Y)
    (J : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M) :
    (P.smoothPurityPullbackComparison f M J e).hom ≫
      (ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient f).hom.app J ≫
      (S P.Coefficient f).map e.hom =
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f).inv.app M := by
  start_mate_proof
  · change
      ((P.smoothPurityPullback f).map e.inv ≫
        (ProEtale.sfDerivedComparisonPullbackIso P.Ring f).hom.app J ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} P.Coefficient) f).inv.app J)) ≫
        (ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient f).hom.app J ≫
        (S P.Coefficient f).map e.hom = _
    simp only [Category.assoc]
    erw [reassoc_of% (sf_pullback_cancel P.Ring f J)]
    erw [NatTrans.naturality_assoc]
    erw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  · finish_mate_proof

private theorem etaleUnitPlus (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (Etale.DerivedCategoryModule A Y)) := by
  start_mate_proof
  · exact ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  · finish_mate_proof

private theorem proUnitPlus (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus (𝟙_ (D A Y)) := by
  start_mate_proof
  · exact ((ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).prop_of_iso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
      (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
        (etaleUnitPlus A Y))).plus
  · finish_mate_proof

attribute [local irreducible] Functor.rightAdjoint Adjunction.ofIsLeftAdjoint

private def standingUnitComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.dualizingComplex A f) ≅ omega A f :=
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y (𝟙_ _) (etaleUnitPlus A Y)
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    ((Etale.rightDerivedUpperShriek A f).mapIso
      (asIso ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _)))) ≪≫
    (G A f).mapIso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)

private def etaleMateSource
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} A)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.dualizingComplex A f ⊗
        (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J) ≅
        (S A f).obj M ⊗ omega A f :=
  ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J ≪≫
    tensorIso (standingUnitComparison A f) ((S A f).mapIso e) ≪≫
    derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (omega A f) ((S A f).obj M)

private theorem unit_inv_comp
    {C D : Type*} [Category C] [Category D] {V : C ⥤ D} {U : D ⥤ C}
    (ad : V ⊣ U) {J K : C} [IsIso (ad.unit.app J)] (a : J ⟶ K) :
    inv (ad.unit.app J) ≫ a ≫ ad.unit.app K = U.map (V.map a) := by
  start_mate_proof
  · have hn : a ≫ ad.unit.app K = ad.unit.app J ≫ U.map (V.map a) :=
      ad.unit.naturality a
    rw [hn, IsIso.inv_hom_id_assoc]
  · finish_mate_proof

private theorem standingUnitComparison_normalization
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (P.diagonalDualizingComparison f).hom ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek P.Coefficient f).map
          (smoothPurityUnitIso P.Coefficient Y).hom) ≫
      (standingUnitComparison P.Coefficient f).hom = (P.modelOrientationUnit f).inv := by
  start_mate_proof
  · let VX := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let H := Etale.rightDerivedUpperShriek P.Coefficient f
    let ad := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y
    let := ProEtale.isIso_derivedComparisonAdjunction_unit_app
      (ModuleCat.{u + 1} P.Coefficient) Y
      (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)
    have hn := unit_inv_comp ad (smoothPurityUnitIso P.Coefficient Y).hom
    let UY := (ProEtale.comparisonLowerStar
      (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
    let VY := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
    let Fe := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) (HasCompactification.compactification f)
    let : Fe.IsLeftAdjoint := inferInstanceAs
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
    let ad₀ := Adjunction.ofIsLeftAdjoint Fe
    let ad₁ : Fe ⊣ H := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
    let c := (ad₀.rightAdjointUniq ad₁).app
      (UY.obj (VY.obj (Etale.ordinaryFiniteUnit P.Coefficient Y)))
    let v := ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
      P.Coefficient Y
    change VX.map (c.hom ≫ H.map (inv (ad.unit.app _))) ≫
        VX.map (H.map (smoothPurityUnitIso P.Coefficient Y).hom) ≫
        (VX.map (H.map (ad.unit.app (𝟙_ _))) ≫
          VX.map (H.map (UY.map v.hom))) =
      VX.map c.hom ≫ VX.map (H.map
        (UY.map (VY.map (smoothPurityUnitIso P.Coefficient Y).hom ≫ v.hom)))
    have he := congrArg
      (fun z ↦ VX.map (c.hom ≫ H.map z ≫ H.map (UY.map v.hom))) hn
    simpa only [Functor.map_comp, Category.assoc] using he
  · finish_mate_proof

private theorem etaleMateSource_normalization
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (J : Etale.DerivedCategoryModule P.Coefficient Y) (M : D P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M) :
    (P.smoothPurityTensorComparison f M J e).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        (((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
          ((Etale.ordinaryFinitePullback P.Coefficient f).obj J)).map
            ((Etale.rightDerivedUpperShriek P.Coefficient f).map
              (smoothPurityUnitIso P.Coefficient Y).hom) ≫
          ((Etale.derivedTensorSymmetry
            (ModuleCat.{u + 1} P.Coefficient) X).hom.app
              ((Etale.ordinaryFinitePullback P.Coefficient f).obj J)).app
                (Etale.dualizingComplex P.Coefficient f)) ≫
      (etaleMateSource P.Coefficient f J M e).hom =
    ((smoothPurityTensor P.Coefficient X).map
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).inv.app M)).app
          (P.diagonalDualizing f) ≫
      ((smoothPurityTensor P.Coefficient X).obj ((S P.Coefficient f).obj M)).map
        (P.modelOrientationUnit f).inv := by
  start_mate_proof
  · let VX := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let N := (Etale.ordinaryFinitePullback P.Coefficient f).obj J
    let O := P.diagonalOrdinaryDualizing f
    let U := Etale.dualizingComplex P.Coefficient f
    have hn := (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) N).hom.naturality
        ((Etale.rightDerivedUpperShriek P.Coefficient f).map
          (smoothPurityUnitIso P.Coefficient Y).hom)
    have hb := comparison_braiding (ModuleCat.{u + 1} P.Coefficient) X N U
    have h := derived_tensor_source_calculation VX
      (P.smoothPurityPullbackComparison f M J e).hom
      (P.diagonalDualizingComparison f).hom
      ((ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient f).hom.app J ≫
        (S P.Coefficient f).map e.hom)
      (standingUnitComparison P.Coefficient f).hom
      ((Etale.rightDerivedUpperShriek P.Coefficient f).map
        (smoothPurityUnitIso P.Coefficient Y).hom)
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) N).app O)
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) N).app U)
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) U).app N) hn hb
      (proEtale_derived_symmetry (ModuleCat.{u + 1} P.Coefficient) X
        ((S P.Coefficient f).obj M) (omega P.Coefficient f))
    rw [smoothPullbackComparison_eq, standingUnitComparison_normalization] at h
    simpa only [N, O, U, VX, smoothPurityTensorComparison, smoothPurityComparisonTensor,
      etaleMateSource, ProEtale.comparisonOpenTensorIso,
      Etale.derivedTensorSymmetry, Etale.ordinaryFinitePullback,
      canonical_symmetry_hom,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
      NatTrans.comp_app, NatIso.ofComponents_hom_app,
      tensorIso_hom, MonoidalCategory.tensorHom_def', MonoidalCategory.tensorHom_def,
      smoothPurityTensor, Etale.derivedTensor, ProEtale.derivedTensor,
      curriedTensor_obj_map, curriedTensor_map_app, curriedTensor_obj_obj,
      Functor.map_comp,
      Category.assoc, whisker_exchange, whisker_exchange_assoc,
      whiskerLeft_comp, whiskerLeft_comp_assoc] using h
  · finish_mate_proof

private def normalizedStandingCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D A Y) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (F A f).obj ((G A f).obj K) ⟶ K :=
  (ProEtale.fixedCompactSupportComparisonIso A
    (HasCompactification.compactification f)).hom.app
      ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj f hK⟩ ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app _) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K

private theorem standingHom_symm
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {M : D A X} (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    {K : D A Y} (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (b : M ⟶ (G A f).obj K) :
    (ProEtale.standingExceptionalHomEquiv A f hM hK).symm b =
      (F A f).map b ≫ normalizedStandingCounit A f K hK := by
  start_mate_proof
  · classical
    let hex : ∃ J : Etale.DerivedCategoryModule A X,
        _root_.DerivedCategory.TStructure.t.plus J ∧
          Nonempty ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J ≅ M) := hM
    let J := Classical.choose hex
    let hJ := (Classical.choose_spec hex).1
    let e := Classical.choice (Classical.choose_spec hex).2
    let VX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let UY := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor
    let H := Etale.rightDerivedUpperShriek A f
    let ad := Etale.rightDerivedUpperShriekAdjunction A f
    let av := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
    let B := ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)
    let hHK := ProEtale.plus_etaleRightDerivedUpperShriek_obj f hK
    obtain ⟨q, hq⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map J
        (H.obj (UY.obj K)) hHK).surjective (e.hom ≫ b)
    change VX.map q = e.hom ≫ b at hq
    have hn := B.inv.naturality (ObjectProperty.homMk q :
      (⟨J, hJ⟩ : _root_.DerivedCategory.Plus _) ⟶ ⟨H.obj (UY.obj K), hHK⟩)
    change VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
        B.inv.app ⟨H.obj (UY.obj K), hHK⟩ =
      B.inv.app ⟨J, hJ⟩ ≫ (F A f).map (VX.map q) at hn
    apply (ProEtale.standingExceptionalHomEquiv A f hM hK).injective
    rw [Equiv.apply_symm_apply]
    symm
    change e.inv ≫ VX.map (ad.homEquiv J (UY.obj K)
      (av.homEquiv _ K (B.inv.app ⟨J, hJ⟩ ≫
        (F A f).map e.hom ≫ (F A f).map b ≫
          normalizedStandingCounit A f K hK))) = b
    have hz : B.inv.app ⟨J, hJ⟩ ≫
        (F A f).map e.hom ≫ (F A f).map b ≫
          normalizedStandingCounit A f K hK =
      VY.map ((ad.homEquiv J (UY.obj K)).symm q) ≫ av.counit.app K := by
      rw [← Functor.map_comp_assoc, ← hq, ← Category.assoc, ← hn]
      simp only [normalizedStandingCounit, Category.assoc]
      change VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
          B.inv.app ⟨H.obj (UY.obj K), hHK⟩ ≫
            B.hom.app ⟨H.obj (UY.obj K), hHK⟩ ≫
              VY.map (ad.counit.app (UY.obj K)) ≫ av.counit.app K = _
      rw [Iso.inv_hom_id_app_assoc]
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hz]
    change e.inv ≫ VX.map (ad.homEquiv J (UY.obj K)
      (av.homEquiv _ K ((av.homEquiv _ K).symm
        ((ad.homEquiv J (UY.obj K)).symm q)))) = b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hq]
    simp
  · finish_mate_proof

private theorem standingHom_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {M N : D A X}
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X N)
    {K : D A Y} (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (a : M ⟶ N) (z : (F A f).obj N ⟶ K) :
    ProEtale.standingExceptionalHomEquiv A f hM hK ((F A f).map a ≫ z) =
      a ≫ ProEtale.standingExceptionalHomEquiv A f hN hK z := by
  start_mate_proof
  · apply (ProEtale.standingExceptionalHomEquiv A f hM hK).symm.injective
    rw [Equiv.symm_apply_apply, standingHom_symm, Functor.map_comp, Category.assoc,
      ← standingHom_symm A f hN hK, Equiv.symm_apply_apply]
  · finish_mate_proof

private theorem standingHom_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (Q : Etale.DerivedCategoryModule A X)
    (hQ : _root_.DerivedCategory.TStructure.t.plus Q)
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (z : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj Q ⟶ J) :
    ProEtale.standingExceptionalHomEquiv A f ⟨Q, hQ, ⟨Iso.refl _⟩⟩ hM
      ((ProEtale.fixedCompactSupportComparisonIso A
        (HasCompactification.compactification f)).hom.app ⟨Q, hQ⟩ ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map z ≫
          e.hom) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv Q J z) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek A f).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app J ≫
            (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.map
              e.hom)) := by
  start_mate_proof
  · let VX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let UY := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor
    let H := Etale.rightDerivedUpperShriek A f
    let ad := Etale.rightDerivedUpperShriekAdjunction A f
    let av := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
    let B := ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)
    let q := ad.homEquiv Q J z ≫ H.map (av.unit.app J ≫ UY.map e.hom)
    have hn := B.hom.naturality (ObjectProperty.homMk q :
      (⟨Q, hQ⟩ : _root_.DerivedCategory.Plus _) ⟶
      ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj f hM⟩)
    change (F A f).map (VX.map q) ≫
        B.hom.app ⟨H.obj (UY.obj M),
          ProEtale.plus_etaleRightDerivedUpperShriek_obj f hM⟩ =
      B.hom.app ⟨Q, hQ⟩ ≫ VY.map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) at hn
    apply (ProEtale.standingExceptionalHomEquiv A f ⟨Q, hQ, ⟨Iso.refl _⟩⟩ hM).symm.injective
    rw [Equiv.symm_apply_apply, standingHom_symm]
    change B.hom.app ⟨Q, hQ⟩ ≫ VY.map z ≫ e.hom =
      (F A f).map (VX.map (ad.homEquiv Q J z) ≫
        VX.map (H.map (av.unit.app J ≫ UY.map e.hom))) ≫
        normalizedStandingCounit A f M hM
    rw [← VX.map_comp]
    change _ = (F A f).map (VX.map q) ≫ normalizedStandingCounit A f M hM
    unfold normalizedStandingCounit
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    change B.hom.app ⟨Q, hQ⟩ ≫ VY.map z ≫ e.hom =
      B.hom.app ⟨Q, hQ⟩ ≫
        VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
          VY.map (ad.counit.app (UY.obj M)) ≫ av.counit.app M
    rw [← VY.map_comp_assoc]
    have hq : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q ≫
        ad.counit.app (UY.obj M) = z ≫ (av.unit.app J ≫ UY.map e.hom) := by
      change (ad.homEquiv Q (UY.obj M)).symm q = _
      dsimp only [q]
      rw [Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
    rw [hq]
    simp only [VY.map_comp, Category.assoc]
    erw [av.counit.naturality]
    erw [reassoc_of% (av.left_triangle_components J)]
    rfl
  · finish_mate_proof

private theorem epsilon_eq_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D A Y) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    epsilon A f K = normalizedStandingCounit A f K hK := by
  start_mate_proof
  · classical
    simp only [epsilon, dif_pos hK]
    rw [standingHom_symm, CategoryTheory.Functor.map_id, Category.id_comp]
  · finish_mate_proof

private theorem standingUnitComparison_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y] :
    (F A f).map (standingUnitComparison A f).hom ≫ epsilon A f (𝟙_ _) =
    (ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)).hom.app
        ⟨Etale.dualizingComplex A f,
          Etale.plus_rightDerivedUpperShriek_obj A f (𝟙_ _) (etaleUnitPlus A Y)⟩ ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom := by
  start_mate_proof
  · let hΩ := Etale.plus_rightDerivedUpperShriek_obj A f (𝟙_ _) (etaleUnitPlus A Y)
    have h := standingHom_comparison A f (Etale.dualizingComplex A f) hΩ
      (𝟙_ _) (𝟙_ _)
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
      (proUnitPlus A Y) ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))
    have hid : (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv
        (Etale.dualizingComplex A f) (𝟙_ _)
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    apply_fun (ProEtale.standingExceptionalHomEquiv A f
      ⟨Etale.dualizingComplex A f, hΩ, ⟨Iso.refl _⟩⟩ (proUnitPlus A Y)).symm at h
    rw [Equiv.symm_apply_apply, standingHom_symm] at h
    rw [epsilon_eq_normalized A f (𝟙_ _) (proUnitPlus A Y)]
    symm
    simpa only [standingUnitComparison, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, Functor.map_comp, G, ProEtale.rightDerivedUpperShriek,
      Functor.comp_map] using h
  · finish_mate_proof

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

private theorem finiteEtalePresentation (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃ J : Etale.DerivedCategoryModule P.Coefficient Y,
      finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos Y J ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) := by
  start_mate_proof
  · classical
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
    let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
    let R := (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor
    have : R.Additive :=
      inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).Additive
    have : PreservesFiniteLimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
    have : PreservesFiniteColimits R :=
      ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
    obtain ⟨a, ha⟩ := hK.1.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.1.bddAbove
    have hz (i : ℤ) (hi : i < min a b ∨ max a b < i) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K) := by
      by_contra hn
      have ha' := ha hn
      have hb' := hb hn
      rcases hi with hi | hi <;> omega
    obtain ⟨J, ⟨eJ⟩⟩ :=
      ((Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K).mpr
        ⟨hK.1.2, min a b, max a b, min_le_max, hz⟩
    let eCJ : E.functor.obj (C.mapDerivedCategory.obj J.obj) ≅ K :=
      ((Functor.mapDerivedCategoryCompIso C R).app J.obj).symm ≪≫ eJ
    let e : C.mapDerivedCategory.obj J.obj ≅ E.inverse.obj K :=
      E.unitIso.app (C.mapDerivedCategory.obj J.obj) ≪≫ E.inverse.mapIso eCJ
    refine ⟨J.obj, ⟨J.property, ?_⟩, ⟨e⟩⟩
    obtain ⟨r, s, ht⟩ := hK.2
    have ht' := torAmplitude_of_iso Y P.Ring eCJ.symm r s ht
    have htp := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      P.Ring Y r s ht.1 (C.mapDerivedCategory.obj J.obj)).mp ht'
    exact ⟨r, s, ht.1,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        (ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory P.Coefficient htp)⟩
  · finish_mate_proof

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.projectionMapOfCompactification ProEtale.projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap ProEtale.rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso
  ProEtale.derivedOpenImmersionLowerShriekProjectionIso

private theorem projection_iso_naturality
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {N N' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (r : N ≅ N') (e : K ≅ K') :
    let Fp := ProEtale.rightDerivedLowerShriek A f
    let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
    let pp := ProEtale.projectionMap A f
    (tensorIso (Fp.mapIso r) e).hom ≫ (pp.app N').app K' =
      (pp.app N).app K ≫ (Fp.mapIso (tensorIso r (Sp.mapIso e))).hom := by
  dsimp only
  let Fp := ProEtale.rightDerivedLowerShriek A f
  let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
  let pp := ProEtale.projectionMap A f
  have hn₁ := congr_app (pp.naturality r.hom) K
  have hn₂ := (pp.app N').naturality e.hom
  change Fp.map r.hom ▷ K ≫ (pp.app N').app K =
    (pp.app N).app K ≫ Fp.map (r.hom ▷ Sp.obj K) at hn₁
  change Fp.obj N' ◁ e.hom ≫ (pp.app N').app K' =
    (pp.app N').app K ≫ Fp.map (N' ◁ Sp.map e.hom) at hn₂
  simp only [tensorIso_hom, Functor.mapIso_hom, MonoidalCategory.tensorHom_def,
    Category.assoc]
  rw [hn₂, ← Category.assoc, hn₁]
  simp only [Category.assoc, ← Fp.map_comp]
  rfl

private theorem tensor_source_cancel
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {Q N N' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (c : Q ≅ N ⊗ (ProEtale.upperStar A f).leftDerivedFunctor.obj K)
    (r : N ≅ N') (e : K ≅ K') :
    let Fp := ProEtale.rightDerivedLowerShriek A f
    let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
    Fp.map (c ≪≫ tensorIso r (Sp.mapIso e) ≪≫
      derivedTensorKoszulSymmetry _ N' (Sp.obj K')).hom ≫
        Fp.map (derivedTensorKoszulSymmetry _ (Sp.obj K') N').hom =
      Fp.map c.hom ≫ (Fp.mapIso (tensorIso r (Sp.mapIso e))).hom := by
  dsimp only
  let Fp := ProEtale.rightDerivedLowerShriek A f
  let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
  have hs := proEtale_derived_symmetry A X N' (Sp.obj K')
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Fp.map_comp, hs, Fp.map_id, Category.comp_id]
  rfl

private theorem genericTensorTranspose_expansion
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (ε : (ProEtale.rightDerivedLowerShriek A f).obj N ⟶ 𝟙_ _) :
    genericTensorTranspose A f N M ε =
      (ProEtale.rightDerivedLowerShriek A f).map
        (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A)
          ((ProEtale.upperStar A f).leftDerivedFunctor.obj M) N).hom ≫
        inverseOnDomain (((ProEtale.projectionMap A f).app N).app M) ≫
          ε ▷ M ≫ (λ_ M).hom := by
  rfl

private theorem tensorTranspose_of_projection_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} A)]
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M)
    [IsIso (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
      (Etale.dualizingComplex A f)).app J)]
    [IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (Etale.dualizingComplex A f))).app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J))]
    (hΩplus : _root_.DerivedCategory.TStructure.t.plus (Etale.dualizingComplex A f))
    (hQ : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj (Etale.dualizingComplex A f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J)))
    (hs :
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f)).app (Etale.dualizingComplex A f)).app J) ≫
        (ProEtale.fixedCompactSupportComparisonIso A
          (HasCompactification.compactification f)).inv.app ⟨_, hQ⟩ ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).map
            (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).obj (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).map
          ((ProEtale.fixedCompactSupportComparisonIso A
            (HasCompactification.compactification f)).inv.app
              ⟨Etale.dualizingComplex A f, hΩplus⟩)).app
                ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J) ≫
        ((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              (Etale.dualizingComplex A f))).app
                ((ProEtale.comparisonUpperStar
                  (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J)) :
    (F A f).map (etaleMateSource A f J M e).hom ≫
      genericTensorTranspose (ModuleCat.{u + 1} A) f
        (omega A f) M (epsilon A f (𝟙_ _)) =
    (ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)).hom.app
      ⟨_, hQ⟩ ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (inv (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
          (Etale.dualizingComplex A f)).app J) ≫
          (Etale.rightDerivedUpperShriekAdjunction A f).counit.app
            (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) :=
      inferInstance
  have hn : (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e).hom ≫
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) =
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) ≫ ((F A
      f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom := by
    exact projection_iso_naturality (ModuleCat.{u + 1} A) f (standingUnitComparison A f) e
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) :=
      inverse_square (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e) ((F A f).mapIso
      (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))) (((ProEtale.projectionMap
      (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) (((ProEtale.projectionMap (ModuleCat.{u +
      1} A) f).app (omega A f)).app M) hn
  have hn' := inverse_square_eq (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e) ((F A
      f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e)))
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) hn
  have hi := invert_projection_square
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
        (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app (Etale.dualizingComplex A f)).app J))
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
        ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
        ⟨_, hQ⟩) ((F A f).mapIso (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f)
        J))
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.dualizingComplex A f))).app J)
    (tensorIso ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification
        f)).app ⟨(Etale.dualizingComplex A f), hΩplus⟩).symm (Iso.refl
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))) (by
      simpa only [F,
        ProEtale.projectionMap, Etale.projectionMap,
        ProEtale.rightDerivedLowerShriek, Etale.rightDerivedLowerShriek,
        ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
        Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
        ProEtale.derivedTensorRightDerivedLowerShriek,
        Etale.derivedTensorRightDerivedLowerShriek, ProEtale.derivedTensor,
        Etale.derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, Functor.comp_obj, Iso.app_hom, Iso.app_inv,
        Functor.mapIso_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom,
        tensorHom_id] using hs)
  have hc := standingUnitComparison_counit A f
  have hc' : ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification
      f)).app ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ≫ (F A f).map (standingUnitComparison A
      f).hom ≫ epsilon A f (𝟙_ _) =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom := by
    simp only [hc, Iso.app_inv]
    erw [Iso.inv_hom_id_app_assoc]
  have ht₀ := congr_app ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      Y).mapDerivedCategoryTensorComparison.naturality
    ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))) J
  have ht : ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J) ≫
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
            ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ▷
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J := by
    rw [comparison_tensor_eq, comparison_tensor_eq]
    change ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J) ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            Y).mapDerivedCategoryTensorComparison.app (𝟙_ _)).app J =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryTensorComparison.app
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj (Etale.dualizingComplex A
          f))).app J ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
            ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ▷
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J at ht₀
    exact ht₀
  have htail :
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
            ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ▷ ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J ≫ (tensorIso ((F A f).mapIso
            (standingUnitComparison A f)) e).hom ≫
        epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
    change _ ≫ _ ≫ ((F A f).map (standingUnitComparison A f).hom ⊗ₘ e.hom) ≫ _ ≫ _ = _
    rw [← tensorHom_id, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [hc', MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc,
      leftUnitor_naturality, ← Category.assoc, ← Category.assoc]
    rw [← reassoc_of% ht]
    simp only [Category.assoc]
    erw [reassoc_of% (comparison_left_unitor A Y J)]
    simp only [Functor.map_comp, Category.assoc]
  have hcancel : (F A f).map (etaleMateSource A f J M e).hom ≫
      (F A f).map (derivedTensorKoszulSymmetry _ ((S A f).obj M) (omega A f)).hom =
      (F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom ≫ ((F A
          f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom := by
    exact tensor_source_cancel (ModuleCat.{u + 1} A) f (ProEtale.comparisonOpenTensorIso A f
        (Etale.dualizingComplex A f) J) (standingUnitComparison A f) e
  rw [genericTensorTranspose_expansion]
  change (F A f).map (etaleMateSource A f J M e).hom ≫
    ((F A f).map (derivedTensorKoszulSymmetry _ ((S A f).obj M) (omega A f)).hom ≫
      inverseOnDomain (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) ≫
          epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom) = _
  rw [← Category.assoc, hcancel]
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso (((ProEtale.projectionMap (ModuleCat.{u
      + 1} A) f).app (omega A f)).app M)), Category.assoc]
  simp only [Functor.mapIso_hom, Iso.app_hom, tensorIso_hom,
    Iso.symm_hom, Iso.refl_hom, Iso.app_inv] at hi
  have htailTensor :
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        (((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
            ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ⊗ₘ 𝟙 (((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) ≫ (tensorIso ((F A f).mapIso
            (standingUnitComparison A f)) e).hom ≫
        epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
    rw [tensorHom_id]
    exact htail
  have hcalc := projection_tail_calculation
    ((F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom) ((F A
        f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom (inv
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M)) (inv
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)))
        (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e).hom
    (epsilon A f (𝟙_ _) ▷ M) (λ_ M).hom
    ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app ⟨_,
        hQ⟩).hom (inv (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
        Y).mapDerivedCategory).map (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
        (Etale.dualizingComplex A f)).app J)))
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.dualizingComplex A f))).hom.app J)
    (((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
        ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ⊗ₘ 𝟙 (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
      (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom) hn' hi htailTensor
  change (F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom ≫ ((F
      A f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom ≫ inv
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) ≫
    epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom = _
  rw [hcalc]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc]
  rfl

private theorem comparison_square_replace
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (B B' : F ≅ G) (hB : B = B') (Q Ω : C) {P T U V : D}
    (p : P ⟶ G.obj Q) (i : F.obj Q ⟶ T) (t : P ⟶ U)
    (δ : (G.obj Ω ⟶ F.obj Ω) → (U ⟶ V)) (q : V ⟶ T)
    (h : p ≫ B'.inv.app Q ≫ i = t ≫ δ (B'.inv.app Ω) ≫ q) :
    p ≫ B.inv.app Q ≫ i = t ≫ δ (B.inv.app Ω) ≫ q := by
  cases hB
  exact h

private theorem tensorTranspose_comparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (hf : f ≫ aY = aX)
    (J : Etale.DerivedCategoryModule P.Coefficient Y) (M : D P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M)
    (hJ : finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y J) :
    (F P.Coefficient f).map (etaleMateSource P.Coefficient f J M e).hom ≫
      genericTensorTranspose (ModuleCat.{u + 1} P.Coefficient) f
        (omega P.Coefficient f) M (epsilon P.Coefficient f (𝟙_ _)) =
    (ProEtale.fixedCompactSupportComparisonIso P.Coefficient
      (HasCompactification.compactification f)).hom.app
      ⟨_, ProEtale.finiteSiteProjectionInput_plus P f
        (Etale.dualizingComplex P.Coefficient f) J
        (dualizing_boundedConstructible P aY f) hJ⟩ ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map
        (inv (((Etale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
          (Etale.dualizingComplex P.Coefficient f)).app J) ≫
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).counit.app
            (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
  let Ω := Etale.dualizingComplex P.Coefficient f
  let hΩ := dualizing_boundedConstructible P aY f
  let hΩplus := ProEtale.finiteSiteProjectionInput_plus_source P X Ω hΩ
  let hQ := ProEtale.finiteSiteProjectionInput_plus P f Ω J hΩ hJ
  have hp := ProEtale.finiteSiteProjections_isIso P aX aY f hf
    (HasCompactification.compactification f) Ω J hΩ hJ
  let : IsIso (((Etale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app Ω).app J) := hp.1
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
        Ω)).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J))
          := hp.2
  have hs := ProEtale.finiteSiteCounitProjectionTransport P aX aY f hf
    (HasCompactification.compactification f) Ω J hΩ hJ
  have hs' := comparison_square_replace
    (ProEtale.fixedCompactSupportComparisonIso P.Coefficient
      (HasCompactification.compactification f))
    (ProEtale.compactSupportSiteComparison P.Coefficient
      (HasCompactification.compactification f))
    (ProEtale.compactSupportComparisonNormalization P.Coefficient
      (HasCompactification.compactification f))
    ⟨_, hQ⟩ ⟨Ω, hΩplus⟩ _ _ _
    (fun z ↦ ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map z).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J))
    _ hs
  exact tensorTranspose_of_projection_square P.Coefficient f J M e hΩplus hQ hs'

private theorem etaleTheta_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (J : Etale.DerivedCategoryModule A Y) :
    (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ J
      (inv (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
        (Etale.dualizingComplex A f)).app J) ≫
        (Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J ≫
          (λ_ J).hom) = Etale.dualizingComplexTensorMap A f J := by
  start_mate_proof
  · simp only [Etale.dualizingComplexTensorMap,
      Etale.lowerShriekRightAdjointUnitTensorMap, Etale.lowerShriekRightAdjointTensorMap,
      Adjunction.projectionTensorMap]
    erw [← Adjunction.homEquiv_naturality_right]
    simp only [Category.assoc]
    rfl
  · finish_mate_proof

private theorem standingTheta_comparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (hf : f ≫ aY = aX)
    (J : Etale.DerivedCategoryModule P.Coefficient Y) (M : D P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M)
    (hJ : finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y J) :
    (etaleMateSource P.Coefficient f J M e).hom ≫ theta P.Coefficient f M =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        (Etale.dualizingComplexTensorMap P.Coefficient f J) ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek P.Coefficient f).map
          ((ProEtale.derivedComparisonAdjunction
            (ModuleCat.{u + 1} P.Coefficient) Y).unit.app J ≫
            (ProEtale.comparisonLowerStar
              (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map e.hom)) := by
  start_mate_proof
  · let A := P.Coefficient
    let Ω := Etale.dualizingComplex A f
    let Q := Ω ⊗ (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J
    let hQ := ProEtale.finiteSiteProjectionInput_plus P f Ω J
      (dualizing_boundedConstructible P aY f) hJ
    let hJplus := ProEtale.finiteSiteProjectionInput_plus_source P Y J hJ.1
    have hM : _root_.DerivedCategory.TStructure.t.plus M :=
      (show ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y M from
        ⟨J, hJplus, ⟨e⟩⟩).plus
    let hVQ : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj Q) :=
      ⟨Q, hQ, ⟨Iso.refl _⟩⟩
    let hW : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
        ((S A f).obj M ⊗ omega A f) := ⟨Q, hQ, ⟨etaleMateSource A f J M e⟩⟩
    have hn := standingHom_left A f hVQ hW hM
      (etaleMateSource A f J M e).hom
      (genericTensorTranspose (ModuleCat.{u + 1} A) f (omega A f) M
        (epsilon A f (𝟙_ _)))
    erw [tensorTranspose_comparison P aX aY f hf J M e hJ,
      standingHom_comparison A f Q hQ J M e hM, etaleTheta_mate] at hn
    symm
    convert hn using 1
    unfold theta genericTheta
    simp only [epsilon, dif_pos hM, dif_pos (show
      _root_.DerivedCategory.TStructure.t.plus (𝟙_ (D A Y)) from proUnitPlus A Y)]
    erw [dif_pos hW]
    rfl
  · finish_mate_proof

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

/-- A single smooth purity map is orientation insertion followed by the standing
projection/counit tensor mate, in the specified coefficient-unit coordinates.
Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 2 and
Step 1's identification of the co-projection constituents
(blueprint: lem-route-composition-single-mate-presentation).

Proof: choose a bounded etale representative of K using constructible origin. The
characterization of smoothPurityTensorMap computes gamma in that representative.
Transpose its theta through the standing Hom bijection: comparison naturality,
the projection comparison and the adjunction triangles give exactly the defining
inverse-projection/counit transpose of CompositionTensorMate.theta. The unit change
is modelOrientationUnit, so tensoring the inverse diagonal orientation becomes
tensoring modelOrientation inverse. Insert the exact/left-derived pullback comparison
and the specified shift reassociation, which together are compositionMateSource.
Faithfulness of comparison identifies the two transposes. Realizing the equality
through the intrinsic coefficient equivalence proves the displayed formula. This
uses no composition assertion and applies equally in relative dimension zero. -/
theorem composition_single_mate_presentation (f : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    letI := P.noetherian (Y ↘ Spec (.of P.field.k))
    letI := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of P.field.k))
    let M := (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K
    P.smoothPurityMap f d K hK =
      (P.compositionMateSource f d K).hom ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((S P.Coefficient f).obj M ◁
            (P.modelOrientation d f (Y ↘ Spec (.of P.field.k))).inv ≫
              theta P.Coefficient f M) := by
  classical
  let := P.noetherian (Y ↘ Spec (.of P.field.k))
  let := Dnc.compactifiable P f (Y ↘ Spec (.of P.field.k))
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let M := (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K
  let T := smoothPurityTensor P.Coefficient X
  let j : (P.smoothPurityPullback f).obj M ≅ (S P.Coefficient f).obj M :=
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f).symm.app M
  obtain ⟨J, hctf, ⟨e⟩⟩ := finiteEtalePresentation P Y K hK
  have htheta : P.smoothPurityTheta f M J e =
      (T.map j.hom).app (P.diagonalDualizing f) ≫
        (T.obj ((S P.Coefficient f).obj M)).map (P.modelOrientationUnit f).inv ≫
          theta P.Coefficient f M := by
    have ht := standingTheta_comparison P (X ↘ Spec (.of P.field.k))
      (Y ↘ Spec (.of P.field.k)) f (by simp) J M e hctf
    have hs := etaleMateSource_normalization P f J M e
    unfold smoothPurityTheta smoothPurityEtaleTheta
    simp only [smoothPurityExceptionalComparison, Iso.refl_inv, Iso.app_inv,
      NatTrans.id_app, Functor.map_comp, Category.assoc]
    simp only [Functor.map_comp] at ht
    erw [Category.comp_id, ← ht]
    simpa only [Functor.map_comp, Category.assoc, Etale.ordinaryFiniteTensor,
      smoothPurityExceptional, ProEtale.rightDerivedUpperShriek, T, j,
      Iso.app_hom, Iso.symm_hom] using
      congrArg (fun z ↦ z ≫ theta P.Coefficient f M) hs
  let b : (T.obj ((P.smoothPurityPullback f).obj M)).obj (P.diagonalTwist X d) ⟶
      (G P.Coefficient f).obj M :=
    (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose
  have hb : b = (T.map j.hom).app (P.diagonalTwist X d) ≫
      ((S P.Coefficient f).obj M ◁
        (P.modelOrientation d f (Y ↘ Spec (.of P.field.k))).inv ≫
          theta P.Coefficient f M) := by
    have hp := (P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec J e
    change b = _ at hp
    rw [hp]
    dsimp only [smoothPurityTensorMapInPresentation]
    rw [htheta]
    have hn := (T.map j.hom).naturality
      (P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv
    change (T.obj ((P.smoothPurityPullback f).obj M)).map _ ≫
        (T.map j.hom).app (P.diagonalDualizing f) =
      (T.map j.hom).app (P.diagonalTwist X d) ≫
        (T.obj ((S P.Coefficient f).obj M)).map _ at hn
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [modelOrientation, Iso.trans_inv, Category.assoc]
    change _ = (T.map j.hom).app (P.diagonalTwist X d) ≫
      (T.obj ((S P.Coefficient f).obj M)).map
        ((P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv ≫
          (P.modelOrientationUnit f).inv) ≫ theta P.Coefficient f M
    rw [Functor.map_comp, Category.assoc]
  change E.functor.map _ ≫ E.functor.map b = _
  rw [hb, E.functor.map_comp]
  simp only [compositionMateSource, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, compositionTensorMapIso,
    Iso.app_hom, CategoryTheory.Functor.map_id, Category.comp_id,
    Iso.refl_hom]
  rfl

end WeilConjectures.PurityFiniteSetting
