/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegrationTransposeCompositionData
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Composition of ordered compact-support integrations

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-iterated-integration).
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u u'

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open Lean Elab Tactic Meta

private theorem integrationStructureProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private meta partial def integrationStructureCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← integrationStructureCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``integrationStructureProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← integrationStructureCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  else
    unless ← isDefEq a b do
      throwError "The projection associativity structures are not definitionally equal"
    return ← mkHEqRefl a


private theorem inverse_compositor_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    {P Q : C} (v : P ⟶ Q) (vi : Q ⟶ P) (hv : v ≫ vi = 𝟙 P)
    {B T : E} (a : G.obj (F.obj Q) ⟶ B) (b : B ⟶ T)
    {U : E} (p : H.obj P ⟶ U) (t : U ⟶ T)
    (hc : α.inv.app Q ≫ a ≫ b = H.map vi ≫ p ≫ t) :
    G.map (F.map v) ≫ a ≫ b = α.hom.app P ≫ p ≫ t := by
  have h := congrArg (fun z ↦ α.hom.app P ≫ H.map v ≫ z) hc
  simpa only [← α.hom.naturality_assoc v, Functor.comp_map,
    Iso.hom_inv_id_app_assoc, ← H.map_comp_assoc, hv, H.map_id,
    Category.id_comp] using h

private theorem swap_assoc
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (L : D ⥤ C)
    (δ : ∀ K N, L.obj (K ⊗ N) ⟶ L.obj K ⊗ L.obj N)
    (π : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ L.obj K))
    (hnM : ∀ {M M'} (v : M ⟶ M') K,
      F.map v ▷ K ≫ π M' K = π M K ≫ F.map (v ▷ L.obj K))
    (hnK : ∀ M {K K'} (v : K ⟶ K'),
      F.obj M ◁ v ≫ π M K' = π M K ≫ F.map (M ◁ L.map v))
    (ha : ∀ M K N, π M K ▷ N ≫ π (M ⊗ L.obj K) N ≫
      F.map (α_ M (L.obj K) (L.obj N)).hom =
      (α_ (F.obj M) K N).hom ≫ π M (K ⊗ N) ≫ F.map (M ◁ δ K N))
    (hb : ∀ K N, L.map (β_ K N).hom ≫ δ N K =
      δ K N ≫ (β_ (L.obj K) (L.obj N)).hom)
    (M : C) (K N : D) :
    let p := fun M K ↦ (β_ K (F.obj M)).hom ≫ π M K ≫
      F.map (β_ (L.obj K) M).inv
    p M (K ⊗ N) ≫ F.map (δ K N ▷ M ≫ (α_ (L.obj K) (L.obj N) M).hom) =
      (α_ K N (F.obj M)).hom ≫ K ◁ p M N ≫ p (L.obj N ⊗ M) K := by
  dsimp only
  simp only [whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc, reassoc_of% hnM]
  have front : (α_ K N (F.obj M)).hom ≫ K ◁ (β_ N (F.obj M)).hom ≫
      (β_ K (F.obj M ⊗ N)).hom =
    (β_ (K ⊗ N) (F.obj M)).hom ≫ F.obj M ◁ (β_ K N).hom ≫
      (α_ (F.obj M) N K).inv := by
    simp only [BraidedCategory.braiding_tensor_right_hom,
      BraidedCategory.braiding_tensor_left_hom, Category.assoc]
  rw [reassoc_of% front]
  have hr : (α_ (F.obj M) N K).inv ≫ π M N ▷ K ≫ π (M ⊗ L.obj N) K =
      π M (N ⊗ K) ≫ F.map (M ◁ δ N K) ≫
        F.map (α_ M (L.obj N) (L.obj K)).inv := by
    rw [← cancel_mono (F.map (α_ M (L.obj N) (L.obj K)).hom)]
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, Category.comp_id]
    rw [ha, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hr, reassoc_of% hnK]
  simp only [← F.map_comp]
  rw [← whiskerLeft_comp_assoc, hb]
  have back : M ◁ (β_ (L.obj K) (L.obj N)).hom ≫
      (α_ M (L.obj N) (L.obj K)).inv ≫
      (β_ (L.obj N) M).inv ▷ L.obj K ≫ (β_ (L.obj K) (L.obj N ⊗ M)).inv =
    (β_ (L.obj K ⊗ L.obj N) M).inv ≫ (α_ (L.obj K) (L.obj N) M).hom := by
    have hc : (α_ (L.obj K) (L.obj N) M).hom ≫
        L.obj K ◁ (β_ (L.obj N) M).hom ≫
        (β_ (L.obj K) (M ⊗ L.obj N)).hom =
      (β_ (L.obj K ⊗ L.obj N) M).hom ≫
        M ◁ (β_ (L.obj K) (L.obj N)).hom ≫
        (α_ M (L.obj N) (L.obj K)).inv := by
      simp only [BraidedCategory.braiding_tensor_right_hom,
        BraidedCategory.braiding_tensor_left_hom, Category.assoc]
    rw [BraidedCategory.braiding_inv_naturality_left]
    apply (cancel_epi (β_ (L.obj K ⊗ L.obj N) M).hom).1
    rw [← reassoc_of% hc]
    simp only [Iso.hom_inv_id_assoc, ← whiskerLeft_comp,
      Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [back, BraidedCategory.braiding_inv_naturality_right_assoc]


private theorem transport_assoc
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) (L Q : D ⥤ C) (e : L ≅ Q)
    (δ : ∀ K N, L.obj (K ⊗ N) ⟶ L.obj K ⊗ L.obj N)
    (p : ∀ M K, K ⊗ F.obj M ⟶ F.obj (L.obj K ⊗ M))
    (hn : ∀ {M M'} (v : M ⟶ M') K,
      K ◁ F.map v ≫ p M' K = p M K ≫ F.map (L.obj K ◁ v))
    (ha : ∀ M K N, p M (K ⊗ N) ≫
      F.map (δ K N ▷ M ≫ (α_ (L.obj K) (L.obj N) M).hom) =
      (α_ K N (F.obj M)).hom ≫ K ◁ p M N ≫ p (L.obj N ⊗ M) K)
    (M : C) (K N : D) :
    let q := fun M K ↦ p M K ≫ F.map (e.hom.app K ▷ M)
    q M (K ⊗ N) ≫
        F.map ((e.inv.app (K ⊗ N) ≫ δ K N ≫
          (e.hom.app K ⊗ₘ e.hom.app N)) ▷ M ≫
          (α_ (Q.obj K) (Q.obj N) M).hom) =
      (α_ K N (F.obj M)).hom ≫ K ◁ q M N ≫ q (Q.obj N ⊗ M) K := by
  dsimp only
  simp only [comp_whiskerRight, Functor.map_comp, whiskerLeft_comp, Category.assoc]
  rw [← F.map_comp_assoc, ← comp_whiskerRight, Iso.hom_inv_id_app]
  simp only [id_whiskerRight, F.map_id, Category.id_comp]
  rw [reassoc_of% hn]
  simp only [← F.map_comp]
  have he : (e.hom.app K ⊗ₘ e.hom.app N) ▷ M ≫
      (α_ (Q.obj K) (Q.obj N) M).hom =
    (α_ (L.obj K) (L.obj N) M).hom ≫
      L.obj K ◁ e.hom.app N ▷ M ≫ e.hom.app K ▷ (Q.obj N ⊗ M) := by
    rw [MonoidalCategory.tensorHom_def', comp_whiskerRight]
    simp only [Category.assoc, associator_naturality_left,
      associator_naturality_middle_assoc]
  rw [he]
  simp only [F.map_comp]
  rw [← F.map_comp_assoc, reassoc_of% ha]

private theorem swap_naturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (L : D ⥤ C)
    (π : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ L.obj K))
    (hn : ∀ {M M'} (v : M ⟶ M') K,
      F.map v ▷ K ≫ π M' K = π M K ≫ F.map (v ▷ L.obj K))
    {M M' : C} (v : M ⟶ M') (K : D) :
    K ◁ F.map v ≫ (β_ K (F.obj M')).hom ≫ π M' K ≫
        F.map (β_ (L.obj K) M').inv =
      ((β_ K (F.obj M)).hom ≫ π M K ≫ F.map (β_ (L.obj K) M).inv) ≫
        F.map (L.obj K ◁ v) := by
  rw [BraidedCategory.braiding_naturality_right_assoc, reassoc_of% hn]
  simp only [Category.assoc, ← F.map_comp]
  rw [BraidedCategory.braiding_inv_naturality_left]

private theorem integration_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (L : D ⥤ C)
    (δ : ∀ K N, L.obj (K ⊗ N) ≅ L.obj K ⊗ L.obj N)
    (p : ∀ M K, K ⊗ F.obj M ⟶ F.obj (L.obj K ⊗ M))
    [∀ M K, IsIso (p M K)]
    (ha : ∀ M K N, p M (K ⊗ N) ≫
      F.map ((δ K N).hom ▷ M ≫ (α_ (L.obj K) (L.obj N) M).hom) =
      (α_ K N (F.obj M)).hom ≫ K ◁ p M N ≫ p (L.obj N ⊗ M) K)
    (M : C) (t : F.obj M ⟶ 𝟙_ D) (K N : D) :
    F.map ((α_ (L.obj K) (L.obj N) M).inv ≫ (δ K N).inv ▷ M) ≫
        inv (p M (K ⊗ N)) ≫ (K ⊗ N) ◁ t ≫ (ρ_ (K ⊗ N)).hom =
      inv (p (L.obj N ⊗ M) K) ≫
        K ◁ (inv (p M N) ≫ N ◁ t ≫ (ρ_ N).hom) := by
  have h : F.map ((α_ (L.obj K) (L.obj N) M).inv ≫ (δ K N).inv ▷ M) ≫
      inv (p M (K ⊗ N)) =
    inv (p (L.obj N ⊗ M) K) ≫ K ◁ inv (p M N) ≫ (α_ K N (F.obj M)).inv := by
    apply (cancel_epi (p (L.obj N ⊗ M) K)).1
    apply (cancel_epi (K ◁ p M N)).1
    apply (cancel_epi (α_ K N (F.obj M)).hom).1
    rw [← reassoc_of% ha]
    simp only [Category.assoc, ← F.map_comp_assoc,
      Iso.hom_inv_id_assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
      F.map_id, Category.id_comp, IsIso.hom_inv_id_assoc,
      ← whiskerLeft_comp_assoc, IsIso.hom_inv_id, whiskerLeft_id]
  rw [reassoc_of% h]
  simp only [whiskerLeft_comp]
  rw [← associator_inv_naturality_right_assoc]
  simp

private theorem projection_assoc_general
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V T : Scheme.{u}} (f : V ⟶ T) [HasCompactification f]
    (M : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (K N : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    let F := rightDerivedLowerShriek B f
    let L := (upperStar B f).leftDerivedFunctor
    let Q := (upperStar B f).mapDerivedCategory
    let e := leftDerivedUpperStarIsoMapDerivedCategory B f
    let p := fun M K ↦ ((derivedTensorSymmetry B T).hom.app K).app (F.obj M) ≫
      ((projectionMap B f).app M).app K ≫
      F.map (((derivedTensorSymmetry B V).inv.app (L.obj K)).app M) ≫
      F.map (((derivedTensor B V).map (e.hom.app K)).app M)
    p M (((derivedTensor B T).obj K).obj N) ≫
      F.map (((derivedTensor B V).map
        (e.inv.app _ ≫ (leftDerivedUpperStarTensorIso B f K N).hom ≫
          ((derivedTensor B V).map (e.hom.app K)).app (L.obj N) ≫
          ((derivedTensor B V).obj (Q.obj K)).map (e.hom.app N))).app M ≫
        (derivedTensorAssociator B V (Q.obj K) (Q.obj N) M).hom) =
      (derivedTensorAssociator B T K N (F.obj M)).hom ≫
        ((derivedTensor B T).obj K).map (p M N) ≫
        p (((derivedTensor B V).obj (Q.obj N)).obj M) K := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf V.smallEtaleTopology B)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf T.smallEtaleTopology B)
  have hs (K N : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
      ((derivedTensorSymmetry B T).hom.app K).app N = (β_ K N).hom := rfl
  have hs' (K N : DerivedCategory (Sheaf V.smallEtaleTopology B)) :
      ((derivedTensorSymmetry B V).inv.app K).app N = (β_ K N).inv := rfl
  let F := rightDerivedLowerShriek B f
  let L := (upperStar B f).leftDerivedFunctor
  let Q := (upperStar B f).mapDerivedCategory
  let π := fun M K ↦ ((projectionMap B f).app M).app K
  let δ := fun K N ↦ (leftDerivedUpperStarTensorIso B f K N).hom
  let p := fun M K ↦ (β_ K (F.obj M)).hom ≫ π M K ≫
    F.map (β_ (L.obj K) M).inv
  have hn : ∀ {M M'} (v : M ⟶ M') K,
      K ◁ F.map v ≫ p M' K = p M K ≫ F.map (L.obj K ◁ v) := by
    intro M M' v K
    exact swap_naturality F L π
      (fun {_ _} v K ↦ congr_app ((projectionMap B f).naturality v) K) v K
  have ha : ∀ M K N, p M (K ⊗ N) ≫
      F.map (δ K N ▷ M ≫ (α_ (L.obj K) (L.obj N) M).hom) =
      (α_ K N (F.obj M)).hom ≫ K ◁ p M N ≫ p (L.obj N ⊗ M) K := by
    intro M K N
    exact swap_assoc F L δ π
      (fun {_ _} v K ↦ congr_app ((projectionMap B f).naturality v) K)
      (fun M {_ _} v ↦ ((projectionMap B f).app M).naturality v)
      (fun M K N ↦ projectionMapOfCompactification_assoc B
        (HasCompactification.compactification f) M K N)
      (fun K N ↦ leftDerivedUpperStar_map_braiding_hom_δ B f K N) M K N
  have h := transport_assoc F L Q (leftDerivedUpperStarIsoMapDerivedCategory B f)
    δ p hn ha M K N
  dsimp only [p, π, δ, F, L, Q] at h
  dsimp only
  simp only [hs, hs', derivedTensor_map_app, derivedTensor_obj_map,
    derivedTensorAssociator_eq, MonoidalCategory.tensorHom_def, Category.assoc] at h ⊢
  run_tac withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `h) | throwError "no h"
    let q ← integrationStructureCongrHEq t (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf


private theorem integration_tensor_general
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V T : Scheme.{u}} (f : V ⟶ T) [HasCompactification f]
    (δ : ∀ K N : DerivedCategory (Sheaf T.smallEtaleTopology B),
      (upperStar B f).mapDerivedCategory.obj (((derivedTensor B T).obj K).obj N) ≅
        ((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj K)).obj
          ((upperStar B f).mapDerivedCategory.obj N))
    (p : ∀ M K, ((derivedTensor B T).obj K).obj ((rightDerivedLowerShriek B f).obj M) ⟶
      (rightDerivedLowerShriek B f).obj
        (((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj K)).obj M))
    [∀ M K, IsIso (p M K)]
    (ha : ∀ M K N, p M (((derivedTensor B T).obj K).obj N) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B V).map (δ K N).hom).app M ≫
          (derivedTensorAssociator B V _ _ M).hom) =
      (derivedTensorAssociator B T K N _).hom ≫
        ((derivedTensor B T).obj K).map (p M N) ≫
        p (((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj N)).obj M) K)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (t : (rightDerivedLowerShriek B f).obj M ⟶ 𝟙_ _)
    (K N : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (rightDerivedLowerShriek B f).map
        ((derivedTensorAssociator B V _ _ M).inv ≫
          ((derivedTensor B V).map (δ K N).inv).app M) ≫
      inv (p M (((derivedTensor B T).obj K).obj N)) ≫
      ((derivedTensor B T).obj (((derivedTensor B T).obj K).obj N)).map t ≫
      (derivedTensorRightUnitor B T _).hom =
    inv (p (((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj N)).obj M) K) ≫
      ((derivedTensor B T).obj K).map
        (inv (p M N) ≫ ((derivedTensor B T).obj N).map t ≫
          (derivedTensorRightUnitor B T N).hom) := by
  exact integration_tensor (rightDerivedLowerShriek B f)
    ((upperStar B f).mapDerivedCategory) δ p ha M t K N

private theorem projection_naturality_general
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (v : M ⟶ M')
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((derivedTensor B Y).obj K).map
        ((rightDerivedLowerShriek B f).map v) ≫
      (((derivedTensorSymmetry B Y).hom.app K).app
        ((rightDerivedLowerShriek B f).obj M') ≫
      ((projectionMap B f).app M').app K ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj M').map
          ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app K)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensorSymmetry B X).inv.app
          ((upperStar B f).mapDerivedCategory.obj K)).app M')) =
    (((derivedTensorSymmetry B Y).hom.app K).app
        ((rightDerivedLowerShriek B f).obj M) ≫
      ((projectionMap B f).app M).app K ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app K)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensorSymmetry B X).inv.app
          ((upperStar B f).mapDerivedCategory.obj K)).app M)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj
          ((upperStar B f).mapDerivedCategory.obj K)).map v) := by
  let F := rightDerivedLowerShriek B f
  let L := (upperStar B f).leftDerivedFunctor
  let D := (upperStar B f).mapDerivedCategory
  let T := derivedTensor B Y
  let U := derivedTensor B X
  let e := leftDerivedUpperStarIsoMapDerivedCategory B f
  let s := derivedTensorSymmetry B X
  have hY := ((derivedTensorSymmetry B Y).hom.app K).naturality
    (F.map v)
  have hP := congr_app ((projectionMap B f).naturality v) K
  change (T.obj K).map (F.map v) ≫ _ = _ ≫ (T.map (F.map v)).app K at hY
  change (T.map (F.map v)).app K ≫ _ = _ ≫ F.map ((U.map v).app (L.obj K)) at hP
  have he : (U.map v).app (L.obj K) ≫ (U.obj M').map (e.hom.app K) ≫
      (s.inv.app (D.obj K)).app M' =
    (U.obj M).map (e.hom.app K) ≫ (s.inv.app (D.obj K)).app M ≫
      (U.obj (D.obj K)).map v := by
    have hn := (U.map v).naturality (e.hom.app K)
    rw [← reassoc_of% hn]
    exact congrArg ((U.obj M).map (e.hom.app K) ≫ ·)
      ((s.inv.app (D.obj K)).naturality v)
  rw [reassoc_of% hY, reassoc_of% hP]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ ((derivedTensorSymmetry B Y).hom.app K).app (F.obj M) ≫
      ((projectionMap B f).app M).app K ≫ F.map z) he


namespace IntegrationComposition

variable {A : Type (u + 1)} [CommRing A] {X Y Z : Scheme.{u}}

private instance symmetry_component_isIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) (K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)) :
    IsIso (((derivedTensorSymmetry B S).hom.app K).app L) :=
  (((derivedTensorSymmetry B S).app K).app L).isIso_hom

private instance symmetry_inv_component_isIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (S : Scheme.{u}) (K L : _root_.DerivedCategory (Sheaf S.smallEtaleTopology B)) :
    IsIso (((derivedTensorSymmetry B S).inv.app K).app L) :=
  (((derivedTensorSymmetry B S).app K).app L).isIso_inv

private theorem projection_eq (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f M K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
        ((projectionMap (ModuleCat.{u + 1} A) f).app M).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M) := by
  dsimp only [compactSupportProjectionMap, compactSupportProjectionMapOfCompactification,
      projectionMap, rightDerivedLowerShriek]

private theorem projection_naturality (f : X ⟶ Y) [HasCompactification f]
    {M M' : DerivedCategoryModule A X} (v : M ⟶ M') (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map v) ≫
      compactSupportProjectionMap A f M' K =
    compactSupportProjectionMap A f M K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map v) := by
  rw [projection_eq, projection_eq]
  exact projection_naturality_general (ModuleCat.{u + 1} A) f v K

private theorem projection_eq_normal (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f M K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      ((projectionMap (ModuleCat.{u + 1} A) f).app M).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).app M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)).app
            M) := by
  rw [projection_eq]
  have hn := congr_app ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) M
  simp only [NatTrans.comp_app, Functor.flip_map_app] at hn
  simp only [← Functor.map_comp]
  rw [hn]

private instance projection_isIso [Finite A] (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (compactSupportProjectionMap A f M K) := by
  have := isIso_projectionMap_of_finite A f
  rw [projection_eq]
  infer_instance

private theorem projection_associativity (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K N : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f M
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj N) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map (pullTensorIso f K N).hom).app M ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ M).hom) =
    (derivedTensorAssociator (ModuleCat.{u + 1} A) Y K N _).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        (compactSupportProjectionMap A f M N) ≫
      compactSupportProjectionMap A f (object f M N) K := by
  rw [projection_eq_normal, projection_eq_normal, projection_eq_normal]
  simpa only [pullTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, NatTrans.comp_app, object, Category.assoc] using
      projection_assoc_general (ModuleCat.{u + 1} A) f M K N

private theorem integration_tensor_law [Finite A] (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶ 𝟙_ _)
    (hP : ∀ K, IsIso (compactSupportProjectionMap A f W K))
    (K N : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ W).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).map (pullTensorIso f K N).inv).app W) ≫
      integration f W t hP (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj N) =
    inv (compactSupportProjectionMap A f (object f W N) K) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map (integration f W t hP N) := by
  exact integration_tensor_general (ModuleCat.{u + 1} A) f
    (pullTensorIso f) (compactSupportProjectionMap A f) (projection_associativity f) W t K N


/-- Ordered integrations compose before applying the adjunction Hom bijections.
Source: cor-pur-vector-bundle-purity.proof.md paragraph 2, node proof steps 2 and 4--6.
(blueprint: lem-pur-iterated-integration).

Proof: Expand integration into inverse projection, tensor of the trace and the unit map.
Apply inverse projection tensor associativity at g* K and Wg; it replaces integration
at their tensor product by projection at g* K followed by tensor of integration at Wg.
Naturality of the g projection in its sheaf argument moves that latter map through the
inverse projection for g. The inverse compact-support composition law identifies the two
successive inverse projections with the inverse projection for f followed by g, transported
by the exact-pullback compositor. The stated reassociation is exactly this transport.
Finally use the trace equation to replace Fg(integration_f) followed by tg with alpha
followed by th. Naturality of the right unitor cancels the terminal tensor unit maps. -/
theorem iterated_integration
    [Finite A] [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (Wf : DerivedCategoryModule A X) (Wg : DerivedCategoryModule A Y)
    (tf : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj Wf ⟶ 𝟙_ _)
    (tg : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj Wg ⟶ 𝟙_ _)
    (th : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj
      (object f Wf Wg) ⟶ 𝟙_ _)
    (hPf : ∀ L : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f Wf L))
    (hPg : ∀ K : DerivedCategoryModule A Z, IsIso (compactSupportProjectionMap A g Wg K))
    (hPh : ∀ K : DerivedCategoryModule A Z,
      IsIso (compactSupportProjectionMap A (f ≫ g) (object f Wf Wg) K))
    (ht : (unboundedEtaleLowerShriekCompIso A f g).hom.app (object f Wf Wg) ≫ th =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map (integration f Wf tf hPf Wg) ≫ tg)
    (K : DerivedCategoryModule A Z) :
    (unboundedEtaleLowerShriekCompIso A f g).hom.app
        (object (f ≫ g) (object f Wf Wg) K) ≫
      integration (f ≫ g) (object f Wf Wg) th hPh K =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (reassociation f g Wf Wg K).hom ≫ integration f Wf tf hPf (object g Wg K)) ≫
      integration g Wg tg hPg K := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
  let Dg := (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
  let T := (derivedTensor (ModuleCat.{u + 1} A) Z).obj K
  let U := (derivedTensor (ModuleCat.{u + 1} A) Y).obj (Dg.obj K)
  let V := derivedTensor (ModuleCat.{u + 1} A) X
  let S := object f Wf Wg
  let α := unboundedEtaleLowerShriekCompIso A f g
  let c := unboundedEtaleUpperStarCompIso A f g
  let v := (V.map (c.hom.app K)).app S
  let vi := (V.map (c.inv.app K)).app S
  let β := integration f Wf tf hPf Wg
  have hv : v ≫ vi = 𝟙 _ := by
    simpa only [v, vi, V, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, NatTrans.comp_app, NatTrans.id_app, Functor.map_comp,
      Functor.map_id] using
      congr_app (Functor.mapIso (derivedTensor (ModuleCat.{u + 1} A) X)
        (c.app K)).hom_inv_id S
  have hc := (compactSupportProjectionMap_comp A f g S K).2
  change α.inv.app _ ≫ G.map (inv (compactSupportProjectionMap A f S (Dg.obj K))) ≫
    inv (compactSupportProjectionMap A g (F.obj S) K) =
      H.map vi ≫ inv (compactSupportProjectionMap A (f ≫ g) S K) ≫ T.map (α.inv.app S) at hc
  have hn := projection_naturality g β K
  have hi : G.map (U.map β) ≫ inv (compactSupportProjectionMap A g Wg K) =
      inv (compactSupportProjectionMap A g (F.obj S) K) ≫ T.map (G.map β) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hn.symm
  have hh : G.map (F.map v) ≫
      G.map (inv (compactSupportProjectionMap A f S (Dg.obj K))) ≫
      inv (compactSupportProjectionMap A g (F.obj S) K) =
    α.hom.app (object (f ≫ g) S K) ≫
      inv (compactSupportProjectionMap A (f ≫ g) S K) ≫ T.map (α.inv.app S) := by
    have h := inverse_compositor_transport F G H α v vi hv
      (G.map (inv (compactSupportProjectionMap A f S (Dg.obj K))))
      (inv (compactSupportProjectionMap A g (F.obj S) K))
      (inv (compactSupportProjectionMap A (f ≫ g) S K)) (T.map (α.inv.app S)) hc
    dsimp only [object, V] at h ⊢
    with_reducible exact h
  let b := (derivedTensorAssociator (ModuleCat.{u + 1} A) X
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj (Dg.obj K))
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj Wg) Wf).inv ≫
      (V.map (pullTensorIso f (Dg.obj K) Wg).inv).app Wf
  have hb := integration_tensor_law f Wf tf hPf (Dg.obj K) Wg
  change F.map b ≫ integration f Wf tf hPf (object g Wg K) =
    inv (compactSupportProjectionMap A f S (Dg.obj K)) ≫ U.map β at hb
  have hr : (reassociation f g Wf Wg K).hom = v ≫ b := rfl
  symm
  rw [hr, F.map_comp, Category.assoc, hb, G.map_comp]
  dsimp only [integration]
  simp only [G.map_comp, Category.assoc]
  rw [reassoc_of% hi, reassoc_of% hh]
  have htrace : α.inv.app S ≫ G.map β ≫ tg = th := by
    rw [← ht, Iso.inv_hom_id_app_assoc]
  change α.hom.app (object (f ≫ g) S K) ≫
      inv (compactSupportProjectionMap A (f ≫ g) S K) ≫
      T.map (α.inv.app S) ≫ T.map (G.map β) ≫ T.map tg ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Z K).hom = _
  have hlast := congrArg T.map htrace
  simp only [T.map_comp] at hlast
  rw [reassoc_of% hlast]

end IntegrationComposition

end AlgebraicGeometry.Etale
