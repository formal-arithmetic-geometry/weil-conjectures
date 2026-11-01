/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionWords
import WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushIdentityPullUnit
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # RefinementProjectionLocalTensor

Source: blueprint fix-prop-projection-formula.proof.md, composition/refinement sentence;
Stacks 0F7B and 0B56 (blueprint: lem-sf-refinement-projection-local-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_unit
    {C : Type*} [Category C] (T : C × C ⥤ C) (U : C ⥤ C)
    (e : U ≅ 𝟭 C) (c : U ≅ U ⋙ U)
    (t : T ⋙ U ⟶ (U.prod U) ⋙ T)
    [IsIso t]
    (hc : ∀ M, c.hom.app M ≫ U.map (e.hom.app M) = 𝟙 _)
    (ht : ∀ M N, c.hom.app (T.obj (M, N)) ≫ U.map (t.app (M, N)) ≫
      t.app (U.obj M, U.obj N) =
      t.app (M, N) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)))
    (M N : C) :
    t.app (M, N) ≫ T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (T.obj (M, N)) := by
  let : U.Faithful := Functor.Faithful.of_iso e.symm
  apply U.map_injective
  apply (cancel_epi (c.hom.app (T.obj (M, N)))).1
  apply (cancel_mono (t.app (M, N))).1
  have hn := t.naturality (Prod.mkHom (e.hom.app M) (e.hom.app N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_obj] at hn
  simp only [U.map_comp, Category.assoc]
  rw [hn, reassoc_of% (ht M N)]
  simp only [← T.map_comp, CategoryTheory.prod_comp, hc]
  change t.app (M, N) ≫ T.map (𝟙 _) = _
  rw [T.map_id]
  erw [Category.comp_id, ← Category.assoc, hc, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_projection
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U V : C ⥤ C} (adj : U ⊣ V) (e : U ≅ 𝟭 C)
    (t : (Functor.postcompose₂.obj U).obj T ⟶
      (((Functor.whiskeringLeft₂ C).obj U).obj U).obj T)
    (ht : ∀ M N, (t.app M).app N ≫
      (T.map (e.hom.app M)).app (U.obj N) ≫ (T.obj M).map (e.hom.app N) =
        e.hom.app ((T.obj M).obj N)) (M N : C) :
    (T.map ((conjugateIsoEquiv adj Adjunction.id e.symm).inv.app M)).app N ≫
      ((adj.rightAdjointProjectionMap t).app M).app N =
    (conjugateIsoEquiv adj Adjunction.id e.symm).inv.app ((T.obj M).obj N) ≫
      V.map ((T.obj M).map (e.inv.app N)) := by
  have h := Adjunction.id.rightAdjointProjectionMap_conjugate (𝟙 _) adj t e.hom
    (fun A B ↦ by
      change e.hom.app ((T.obj A).obj B) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact (ht A B).symm) M N
  have hp : ((Adjunction.id.rightAdjointProjectionMap (𝟙 _ :
      (Functor.postcompose₂.obj (𝟭 C)).obj T ⟶
        (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj (𝟭 C)).obj T)).app M).app N =
      𝟙 _ := by
    simp [Adjunction.rightAdjointProjectionMap, Adjunction.homEquiv, Adjunction.id]
  rw [hp] at h
  have hg : (conjugateEquiv Adjunction.id adj e.hom) =
      (conjugateIsoEquiv adj Adjunction.id e.symm).inv := rfl
  rw [hg] at h
  apply (cancel_mono (V.map ((T.obj M).map (e.hom.app N)))).1
  simpa only [Category.assoc, ← V.map_comp, ← (T.obj M).map_comp,
    e.inv_hom_id_app, (T.obj M).map_id, V.map_id, Category.comp_id,
    Category.id_comp, Functor.id_obj] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_projection_normalized
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U V : C ⥤ C} (adj : U ⊣ V) (e : U ≅ 𝟭 C)
    (t : (Functor.postcompose₂.obj U).obj T ⟶
      (((Functor.whiskeringLeft₂ C).obj U).obj U).obj T)
    (ht : ∀ M N, (t.app M).app N ≫
      (T.map (e.hom.app M)).app (U.obj N) ≫ (T.obj M).map (e.hom.app N) =
        e.hom.app ((T.obj M).obj N))
    (a : V ≅ 𝟭 C) (ha : a = conjugateIsoEquiv adj Adjunction.id e.symm)
    (pi : ∀ M N, (T.obj (V.obj M)).obj N ⟶ V.obj ((T.obj M).obj (U.obj N)))
    (hpi : ∀ M N, pi M N = ((adj.rightAdjointProjectionMap t).app M).app N)
    (M N : C) :
    (T.map (a.inv.app M)).app N ≫ pi M N =
      a.inv.app ((T.obj M).obj N) ≫ V.map ((T.obj M).map (e.inv.app N)) := by
  rw [ha, hpi]
  exact identity_projection T adj e t ht M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalize_mate
    {X B C : Type*} [Category X] [Category B] [Category C]
    (TX : X × X ⥤ X) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (J : X ⥤ B) (J' : X ⥤ C) (S : B ⥤ C)
    (P : B ⥤ X) (Q : C ⥤ B) (H : C ⥤ X)
    (U V : X ⥤ X) (e : U ≅ 𝟭 X) (a : 𝟭 X ⟶ V)
    (g : V ⋙ J' ⟶ J ⋙ S) (sq : H ⋙ U ≅ Q ⋙ P)
    (d : J.prod (𝟭 B) ⋙ TB ⟶ (𝟭 X).prod P ⋙ TX ⋙ J)
    (d' : J'.prod (𝟭 C) ⋙ TC ⟶ (𝟭 X).prod H ⋙ TX ⋙ J')
    (pi₀ : ∀ K N, TX.obj (V.obj K, N) ⟶ V.obj (TX.obj (K, U.obj N)))
    (pi : ∀ M N, TC.obj (S.obj M, N) ⟶ S.obj (TB.obj (M, Q.obj N)))
    (hi : ∀ K N, TX.map (Prod.mkHom (a.app K) (𝟙 N)) ≫ pi₀ K N =
      a.app (TX.obj (K, N)) ≫ V.map (TX.map (Prod.mkHom (𝟙 K) (e.inv.app N))))
    (hm : ∀ K N, d'.app (V.obj K, N) ≫ J'.map (pi₀ K (H.obj N)) ≫
      J'.map (V.map (TX.map (Prod.mkHom (𝟙 K) (sq.hom.app N)))) ≫
      g.app (TX.obj (K, P.obj (Q.obj N))) =
      TC.map (Prod.mkHom (g.app K) (𝟙 N)) ≫ pi (J.obj K) N ≫
        S.map (d.app (K, Q.obj N)))
    (K : X) (N : C) :
    d'.app (K, N) ≫ (identityNormalize J J' V S a g).app (TX.obj (K, H.obj N)) ≫
      S.map (J.map (TX.map (Prod.mkHom (𝟙 K)
        (e.inv.app (H.obj N) ≫ sq.hom.app N)))) =
      TC.map (Prod.mkHom ((identityNormalize J J' V S a g).app K) (𝟙 N)) ≫
        pi (J.obj K) N ≫ S.map (d.app (K, Q.obj N)) := by
  have hn := d'.naturality (Prod.mkHom (a.app K) (𝟙 N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hn
  simp only [H.map_id] at hn
  have ht : TX.map (Prod.mkHom (a.app K) (𝟙 (H.obj N))) ≫
      pi₀ K (H.obj N) ≫
      V.map (TX.map (Prod.mkHom (𝟙 K) (sq.hom.app N))) =
      a.app (TX.obj (K, H.obj N)) ≫
        V.map (TX.map (Prod.mkHom (𝟙 K)
          (e.inv.app (H.obj N) ≫ sq.hom.app N))) := by
    rw [← Category.assoc, hi]
    simp only [Category.assoc, ← V.map_comp, ← TX.map_comp,
      CategoryTheory.prod_comp, Category.id_comp]
  have h := congrArg
    (fun v ↦ TC.map (Prod.mkHom (J'.map (a.app K)) (𝟙 N)) ≫ v) (hm K N)
  simp only [← Category.assoc] at h
  rw [hn] at h
  simp only [Category.assoc] at h
  rw [← J'.map_comp_assoc, ← J'.map_comp_assoc] at h
  simp only [Category.assoc] at h
  rw [ht, J'.map_comp] at h
  have hg := g.naturality (TX.map (Prod.mkHom (𝟙 K)
    (e.inv.app (H.obj N) ≫ sq.hom.app N)))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hg
  simp only [Category.assoc] at h
  rw [hg] at h
  simp only [identityNormalize, Functor.id_obj, Category.assoc] at h ⊢
  rw [tensorFirstComp]
  simpa only [Category.assoc] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_second_comp {C : Type*} [Category C] (T : C × C ⥤ C)
    (K : C) {M N P : C} (v : M ⟶ N) (w : N ⟶ P) :
    T.map (Prod.mkHom (𝟙 K) (v ≫ w)) =
      T.map (Prod.mkHom (𝟙 K) v) ≫ T.map (Prod.mkHom (𝟙 K) w) := by
  rw [← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_local
    {X B C Y : Type*} [Category X] [Category B] [Category C] [Category Y]
    (TX : X × X ⥤ X) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (J : X ⥤ B) (J' : X ⥤ C) (S : B ⥤ C)
    (P : B ⥤ X) (Q : C ⥤ B) (H : C ⥤ X) (R : Y ⥤ C) (R' : Y ⥤ B)
    (F : Y ⥤ X) (g : J' ⟶ J ⋙ S)
    (d : J.prod (𝟭 B) ⋙ TB ⟶ (𝟭 X).prod P ⋙ TX ⋙ J)
    (d' : J'.prod (𝟭 C) ⋙ TC ⟶ (𝟭 X).prod H ⋙ TX ⋙ J')
    (pi : ∀ M N, TC.obj (S.obj M, N) ⟶ S.obj (TB.obj (M, Q.obj N)))
    (t : H ⟶ Q ⋙ P) (v : R ⋙ Q ⟶ R')
    (b : R' ⋙ P ⟶ F) (b' : R ⋙ H ⟶ F)
    (ht : ∀ L, t.app (R.obj L) ≫ P.map (v.app L) ≫ b.app L = b'.app L)
    (hm : ∀ K N, d'.app (K, N) ≫ g.app (TX.obj (K, H.obj N)) ≫
      S.map (J.map (TX.map (Prod.mkHom (𝟙 K) (t.app N)))) =
      TC.map (Prod.mkHom (g.app K) (𝟙 N)) ≫ pi (J.obj K) N ≫
        S.map (d.app (K, Q.obj N))) (K : X) (L : Y) :
    (d'.app (K, R.obj L) ≫ J'.map (TX.map (Prod.mkHom (𝟙 K) (b'.app L)))) ≫
      g.app (TX.obj (K, F.obj L)) =
      TC.map (Prod.mkHom (g.app K) (𝟙 (R.obj L))) ≫
        (pi (J.obj K) (R.obj L) ≫
          S.map (TB.map (Prod.mkHom (𝟙 (J.obj K)) (v.app L)))) ≫
        S.map (d.app (K, R'.obj L) ≫ J.map
          (TX.map (Prod.mkHom (𝟙 K) (b.app L)))) := by
  have h := congrArg (fun v₀ ↦ v₀ ≫ S.map (J.map (TX.map (Prod.mkHom (𝟙 K)
    (P.map (v.app L) ≫ b.app L))))) (hm K (R.obj L))
  simp only [Category.assoc, ← S.map_comp, ← J.map_comp, ← TX.map_comp,
    CategoryTheory.prod_comp, Category.id_comp] at h
  rw [← Category.assoc, ht] at h
  have hn := d.naturality (Prod.mkHom (𝟙 K) (v.app L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at hn
  simp only [J.map_id, Functor.comp_obj, Functor.id_obj] at hn
  rw [tensor_second_comp, J.map_comp] at h
  rw [← reassoc_of% hn] at h
  simpa only [Category.assoc, g.naturality, Functor.comp_map, Functor.comp_obj,
    Functor.prod_obj, Functor.id_obj, S.map_comp] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private def uncurry_tensor_iso {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    (U : C ⥤ C)
    (t : (Functor.postcompose₂.obj U).obj T ≅
      (((Functor.whiskeringLeft₂ C).obj U).obj U).obj T) :
    Functor.uncurry.obj T ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj T :=
  NatIso.ofComponents (fun M ↦ (t.app M.1).app M.2) (by
    intro M N v
    have h := (Functor.uncurry.map t.hom).naturality v
    dsimp only [Functor.uncurry, Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_map, Functor.comp_obj,
      Functor.prod_map, Functor.prod_obj, Functor.whiskerLeft, Functor.whiskerRight] at h ⊢
    simpa only [Functor.map_comp, Iso.app_hom] using h)

attribute [-instance] CategoryTheory.catToReflQuiver in
private def uncurry_open_map
    {X Y : Type*} [Category X] [Category Y]
    (TX : X ⥤ X ⥤ X) (TY : Y ⥤ Y ⥤ Y) (J : X ⥤ Y) (P : Y ⥤ X)
    (d : (((Functor.whiskeringLeft₂ Y).obj J).obj (𝟭 Y)).obj TY ⟶
      (Functor.postcompose₂.obj J).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj P).obj TX)) :
    J.prod (𝟭 Y) ⋙ Functor.uncurry.obj TY ⟶
      (𝟭 X).prod P ⋙ Functor.uncurry.obj TX ⋙ J where
  app M := (d.app M.1).app M.2
  naturality M N v := by
    have h := (Functor.uncurry.map d).naturality v
    dsimp only [Functor.uncurry, Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_map, Functor.comp_obj,
      Functor.prod_map, Functor.prod_obj, Functor.whiskerLeft, Functor.whiskerRight] at h ⊢
    simpa only [Functor.map_comp, Iso.app_hom] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem uncurry_first {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {M N : C} (v : M ⟶ N) (L : C) :
    (Functor.uncurry.obj T).map (Prod.mkHom v (𝟙 L)) = (T.map v).app L := by
  rw [Functor.uncurry_obj_map, (T.obj N).map_id, Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem uncurry_second {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    (K : C) {M N : C} (v : M ⟶ N) :
    (Functor.uncurry.obj T).map (Prod.mkHom (𝟙 K) v) = (T.obj K).map v := by
  rw [Functor.uncurry_obj_map, T.map_id, NatTrans.id_app, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem dependent_congr_heq {I : Sort*} {D : I → Sort*}
    (v : ∀ i, D i) {i j : I} (h : i = j) : HEq (v i) (v j) := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem retype_identity_projection
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U V U' V' : C ⥤ C} (hU : U = U') (hV : V = V')
    (e : U ≅ 𝟭 C) (e' : U' ≅ 𝟭 C) (he : HEq e e')
    (a : V ≅ 𝟭 C) (a' : V' ≅ 𝟭 C) (ha : HEq a a')
    (pi : ∀ M N, (T.obj (V.obj M)).obj N ⟶ V.obj ((T.obj M).obj (U.obj N)))
    (pi' : ∀ M N, (T.obj (V'.obj M)).obj N ⟶ V'.obj ((T.obj M).obj (U'.obj N)))
    (hpi : HEq pi pi')
    (h : ∀ M N, (T.map (a.inv.app M)).app N ≫ pi M N =
      a.inv.app ((T.obj M).obj N) ≫ V.map ((T.obj M).map (e.inv.app N)))
    (M N : C) :
    (Functor.uncurry.obj T).map (Prod.mkHom (a'.inv.app M) (𝟙 N)) ≫ pi' M N =
      a'.inv.app ((Functor.uncurry.obj T).obj (M, N)) ≫
        V'.map ((Functor.uncurry.obj T).map (Prod.mkHom (𝟙 M) (e'.inv.app N))) := by
  cases hU
  cases hV
  cases he
  cases ha
  cases hpi
  simpa only [uncurry_first T, uncurry_second T, Functor.uncurry_obj_obj] using h M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_unit_index
    {I C : Type*} [Category C] (T : C × C ⥤ C) (U : I → C ⥤ C)
    (t : ∀ i, T ⋙ U i ≅ ((U i).prod (U i)) ⋙ T)
    {i j : I} (h : i = j) (e : U j ≅ 𝟭 C) (c : U i ≅ U j ⋙ U j)
    (hc : ∀ M, (indexIso U h.symm).hom.app M ≫
      c.hom.app M ≫ (U j).map (e.hom.app M) = 𝟙 _)
    (ht : ∀ M N, c.hom.app (T.obj (M, N)) ≫ (U j).map ((t j).hom.app (M, N)) ≫
      (t j).hom.app ((U j).obj M, (U j).obj N) =
      (t i).hom.app (M, N) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app N)))
    (M N : C) :
    (t j).hom.app (M, N) ≫ T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (T.obj (M, N)) := by
  cases h
  simp only [indexIso, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hc
  exact tensor_identity_unit T (U i) e c (t i).hom hc ht M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_comp_congr_left
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X Y Z : G} {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z) (M : D Z) :
    (indexIso P (congrArg (· ≫ g) h)).hom.app M ≫ (c f' g).hom.app M =
      (c f g).hom.app M ≫ (indexIso P h).hom.app ((P g).obj M) := by
  cases h
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_comp_congr_right
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X Y Z : G} (f : X ⟶ Y) {g g' : Y ⟶ Z} (h : g = g') (M : D Z) :
    (indexIso P (congrArg (f ≫ ·) h)).hom.app M ≫ (c f g').hom.app M =
      (c f g).hom.app M ≫ (P f).map ((indexIso P h).hom.app M) := by
  cases h
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem indexIso_trans_app
    {I C D : Type*} [Category C] [Category D] (P : I → C ⥤ D)
    {i j k : I} (h : i = j) (h' : j = k) (M : C) :
    (indexIso P h).hom.app M ≫ (indexIso P h').hom.app M =
      (indexIso P (h.trans h')).hom.app M := by
  cases h
  cases h'
  simp [indexIso]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_left_unit
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X : G} (e : P (𝟙 X) ≅ 𝟭 (D X))
    (he : ∀ M, (indexIso P (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c (𝟙 X) (𝟙 X)).hom.app M ≫ (P (𝟙 X)).map (e.hom.app M) = 𝟙 _)
    {Y : G} (f : X ⟶ Y) (M : D Y)
    (ha : (c (𝟙 X) ((𝟙 X) ≫ f)).hom.app M ≫
      (P (𝟙 X)).map ((c (𝟙 X) f).hom.app M) =
      (indexIso P (Category.assoc (𝟙 X) (𝟙 X) f).symm).hom.app M ≫
        (c ((𝟙 X) ≫ (𝟙 X)) f).hom.app M ≫
        (c (𝟙 X) (𝟙 X)).hom.app ((P f).obj M)) :
    (indexIso P (Category.id_comp f).symm).hom.app M ≫ (c (𝟙 X) f).hom.app M ≫
      e.hom.app ((P f).obj M) = 𝟙 _ := by
  let U := P (𝟙 X)
  let k := indexIso P (Category.id_comp f).symm ≪≫ c (𝟙 X) f
  let ci := indexIso P (Category.id_comp (𝟙 X)).symm ≪≫ c (𝟙 X) (𝟙 X)
  have hk : k.hom.app M ≫ U.map (k.hom.app M) =
      k.hom.app M ≫ ci.hom.app ((P f).obj M) := by
    dsimp only [k, ci, Iso.trans_hom, NatTrans.comp_app]
    simp only [U, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% (pull_comp_congr_right D P c (𝟙 X) (Category.id_comp f).symm M)]
    rw [ha]
    have hl := pull_comp_congr_left D P c (Category.id_comp (𝟙 X)).symm f M
    rw [← reassoc_of% hl]
    simp only [← Category.assoc, indexIso_trans_app]
  have hh := (cancel_epi (k.hom.app M)).1 hk
  let : U.Faithful := Functor.Faithful.of_iso e.symm
  have hz : U.map (k.hom.app M ≫ e.hom.app ((P f).obj M)) = U.map (𝟙 _) := by
    rw [U.map_comp, hh, U.map_id]
    simpa only [ci, U, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
      using he ((P f).obj M)
  have hz' := U.map_injective hz
  simpa only [k, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using hz'

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem indexIso_refl {I C : Type*} [Category C] (P : I → C) (i : I) :
    indexIso P (rfl : i = i) = Iso.refl (P i) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_triangle_transport
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X B C Y : G} (k : X ⟶ B) (v : B ⟶ C) (p : C ⟶ Y)
    (i : X ⟶ C) (q : B ⟶ Y) (f : X ⟶ Y)
    (hi : k ≫ v = i) (hq : v ≫ p = q) (hf : k ≫ q = f) (hf' : i ≫ p = f)
    (M : D Y)
    (ha : (c k (v ≫ p)).hom.app M ≫ (P k).map ((c v p).hom.app M) =
      (indexIso P (Category.assoc k v p).symm).hom.app M ≫
        (c (k ≫ v) p).hom.app M ≫ (c k v).hom.app ((P p).obj M)) :
    (indexIso P hi.symm).hom.app ((P p).obj M) ≫
      (c k v).hom.app ((P p).obj M) ≫
      (P k).map ((c v p).inv.app M ≫ (indexIso P hq).hom.app M) ≫
      (c k q).inv.app M ≫ (indexIso P hf).hom.app M =
    (c i p).inv.app M ≫ (indexIso P hf').hom.app M := by
  subst i
  subst q
  subst f
  simp only [indexIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  apply (cancel_epi ((indexIso P (Category.assoc k v p).symm).hom.app M ≫
    (c (k ≫ v) p).hom.app M)).1
  simp only [Category.assoc]
  rw [← reassoc_of% ha]
  simp only [← (P k).map_comp_assoc, Iso.hom_inv_id_app]
  rw [(P k).map_id]
  simp only [Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalize_square
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X B C : G} (k : X ⟶ B) (v : B ⟶ C) (i : X ⟶ C) (h : k ≫ v = i)
    (e : P (𝟙 X) ≅ 𝟭 (D X))
    (he : ∀ M, (indexIso P (Category.id_comp i).symm).hom.app M ≫
      (c (𝟙 X) i).hom.app M ≫ e.hom.app ((P i).obj M) = 𝟙 _)
    (M : D C) :
    e.inv.app ((P i).obj M) ≫ (c (𝟙 X) i).inv.app M ≫
      (indexIso P (h.trans (Category.id_comp i).symm).symm).hom.app M ≫
      (c k v).hom.app M =
      (indexIso P h.symm).hom.app M ≫ (c k v).hom.app M := by
  have hi : e.inv.app ((P i).obj M) ≫ (c (𝟙 X) i).inv.app M =
      (indexIso P (Category.id_comp i).symm).hom.app M := by
    apply (cancel_mono ((c (𝟙 X) i).hom.app M ≫ e.hom.app ((P i).obj M))).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    exact (he M).symm
  rw [← Category.assoc, ← Category.assoc, hi]
  simp only [Category.assoc]
  rw [← Category.assoc, indexIso_trans_app]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_iso_map' {C : Type*} [Category C]
    {U : C ⥤ C} (e : U ≅ 𝟭 C) (M : C) :
    U.map (e.hom.app M) = e.hom.app (U.obj M) := by
  apply (cancel_mono (e.hom.app M)).1
  exact e.hom.naturality (e.hom.app M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_projection_uncurried
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {U V : C ⥤ C} (adj : U ⊣ V) (e : U ≅ 𝟭 C)
    (t : T ⋙ U ≅ U.prod U ⋙ T)
    (ht : ∀ M N, t.hom.app (M, N) ≫
      T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) = e.hom.app (T.obj (M, N)))
    (M N : C) :
    T.map (Prod.mkHom
      ((conjugateIsoEquiv adj Adjunction.id e.symm).inv.app M) (𝟙 N)) ≫
      ((adj.rightAdjointProjectionMap (T_C := Functor.curryObj T) (T_D := Functor.curryObj T)
        (Functor.curry.mapIso t ≪≫ Functor.curryObjProdComp U U T).hom).app M).app N =
    (conjugateIsoEquiv adj Adjunction.id e.symm).inv.app (T.obj (M, N)) ≫
      V.map (T.map (Prod.mkHom (𝟙 M) (e.inv.app N))) := by
  apply identity_projection (Functor.curryObj T) adj e
    (Functor.curry.mapIso t ≪≫ Functor.curryObjProdComp U U T).hom ?_ M N
  intro M N
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.curry_map_app_app, Functor.curryObjProdComp_hom_app_app]
  erw [Category.comp_id]
  dsimp only [Functor.curryObj]
  rw [← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp]
  erw [Category.comp_id (e.hom.app M)]
  exact ht M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_projection_uncurried_normalized
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {U V : C ⥤ C} (adj : U ⊣ V) (e : U ≅ 𝟭 C)
    (t : T ⋙ U ≅ U.prod U ⋙ T)
    (ht : ∀ M N, t.hom.app (M, N) ≫
      T.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) = e.hom.app (T.obj (M, N)))
    (a : V ≅ 𝟭 C) (ha : a = conjugateIsoEquiv adj Adjunction.id e.symm)
    (pi : ∀ M N, T.obj (V.obj M, N) ⟶ V.obj (T.obj (M, U.obj N)))
    (hpi : ∀ M N, pi M N = ((adj.rightAdjointProjectionMap
      (T_C := Functor.curryObj T) (T_D := Functor.curryObj T)
      (Functor.curry.mapIso t ≪≫ Functor.curryObjProdComp U U T).hom).app M).app N)
    (M N : C) :
    T.map (Prod.mkHom (a.inv.app M) (𝟙 N)) ≫ pi M N =
      a.inv.app (T.obj (M, N)) ≫ V.map (T.map (Prod.mkHom (𝟙 M) (e.inv.app N))) := by
  rw [ha, hpi]
  exact identity_projection_uncurried T adj e t ht M N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_unit_app
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X : G} (e : P (𝟙 X) ≅ 𝟭 (D X))
    (h : eqToIso (congrArg P (Category.id_comp (𝟙 X)).symm) ≪≫
      c (𝟙 X) (𝟙 X) ≪≫ Functor.isoWhiskerLeft (P (𝟙 X)) e ≪≫
        Functor.rightUnitor (P (𝟙 X)) = Iso.refl _) (M : D X) :
    (indexIso P (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c (𝟙 X) (𝟙 X)).hom.app M ≫ (P (𝟙 X)).map (e.hom.app M) = 𝟙 _ := by
  have hh := congrArg (fun q ↦ q.hom.app M) h
  rw [eqToIso_congrArg_indexIso P (Category.id_comp (𝟙 X)).symm] at hh
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app, ← identity_iso_map' e] at hh
  erw [Category.comp_id ((P (𝟙 X)).map (e.hom.app M))] at hh
  exact hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_assoc_app
    {G : Type*} [Category G] (D : G → Type*) [∀ X, Category (D X)]
    (P : ∀ {X Y : G}, (X ⟶ Y) → D Y ⥤ D X)
    (c : ∀ {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {W X Y Z : G} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (ha : c f (g ≫ h) ≪≫ Functor.isoWhiskerRight (c g h) (P f) =
      eqToIso (congrArg P (Category.assoc f g h).symm) ≪≫ c (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (P h) (c f g)) (M : D Z) :
    (c f (g ≫ h)).hom.app M ≫ (P f).map ((c g h).hom.app M) =
      (indexIso P (Category.assoc f g h).symm).hom.app M ≫
        (c (f ≫ g) h).hom.app M ≫ (c f g).hom.app ((P h).obj M) := by
  rw [eqToIso_congrArg_indexIso P (Category.assoc f g h).symm] at ha
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      using congrArg (fun q ↦ q.hom.app M) ha

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem indexIso_comp_eq {I J C : Type*} [Category C]
    (P : I → C) (Q : J → I) {i j : J} (h : i = j) :
    indexIso (fun j ↦ P (Q j)) h = indexIso P (congrArg Q h) := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_unit_curried
    {I C : Type*} [Category C] (T : C ⥤ C ⥤ C) (U : I → C ⥤ C)
    (t : ∀ i, (Functor.postcompose₂.obj (U i)).obj T ≅
      (((Functor.whiskeringLeft₂ C).obj (U i)).obj (U i)).obj T)
    {i j : I} (h : i = j) (e : U j ≅ 𝟭 C) (c : U i ≅ U j ⋙ U j)
    (hc : ∀ M, (indexIso U h.symm).hom.app M ≫
      c.hom.app M ≫ (U j).map (e.hom.app M) = 𝟙 _)
    (ht : ∀ M N, c.hom.app ((T.obj M).obj N) ≫
      (U j).map (((t j).hom.app M).app N) ≫
      ((t j).hom.app ((U j).obj M)).app ((U j).obj N) =
      ((t i).hom.app M).app N ≫ (T.map (c.hom.app M)).app ((U i).obj N) ≫
        (T.obj ((U j).obj ((U j).obj M))).map (c.hom.app N))
    (M N : C) :
    ((t j).hom.app M).app N ≫ (T.map (e.hom.app M)).app ((U j).obj N) ≫
      (T.obj M).map (e.hom.app N) = e.hom.app ((T.obj M).obj N) := by
  have hu := tensor_identity_unit_index (Functor.uncurry.obj T) U
    (fun i ↦ uncurry_tensor_iso T (U i) (t i)) h e c hc (by
      intro M N
      simpa only [uncurry_tensor_iso, NatIso.ofComponents_hom_app, Iso.app_hom,
        Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map] using ht M N) M N
  simpa only [uncurry_tensor_iso, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map] using hu

section FiniteProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] ordinary derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] Functor.mapDerivedCategory
  leftDerivedUpperStarComp leftDerivedUpperStarTensorNatIso
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarTensorComparison derivedTensor
  leftDerivedUpperStarId

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory instCategoryDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_congr_index
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h = indexIso (ProperOpenPull A) h := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_tensor_identity (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ht : OrdinaryTensorComposition F A) (X : Spaces F)
    (K N : ProperOpenDerived A X.obj.left) :
    ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A)
        (𝟙 X : X ⟶ X).hom.left).hom.app K).app N ≫
      ((ProperOpenTensor A X.obj.left).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left).hom.app K)).app
          ((ProperOpenPull A (𝟙 X : X ⟶ X).hom.left).obj N) ≫
      ((ProperOpenTensor A X.obj.left).obj K).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left).hom.app N) =
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left).hom.app
      (((ProperOpenTensor A X.obj.left).obj K).obj N) := by
  let e := leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left
  have hu := tensor_identity_unit_curried (ProperOpenTensor A X.obj.left)
    (fun g : X ⟶ X ↦ ProperOpenPull A g.hom.left)
    (fun g ↦ leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) g.hom.left)
    (Category.id_comp (𝟙 X)) e ((ordinary F A).pComp (𝟙 X) (𝟙 X)) (by
      intro M
      rw [indexIso_comp_eq (ProperOpenPull A) (fun g : X ⟶ X ↦ g.hom.left)
        (Category.id_comp (𝟙 X)).symm]
      change (indexIso (ProperOpenPull A)
        (Category.id_comp (𝟙 X.obj.left)).symm).hom.app M ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          (𝟙 X.obj.left) (𝟙 X.obj.left)).hom.app M ≫
        (ProperOpenPull A (𝟙 X.obj.left)).map (e.hom.app M) = 𝟙 _
      have h := leftDerivedUpperStarComp_id_right_app
        (A := ModuleCat.{u + 1} A) (𝟙 X.obj.left) M
      rw [finite_congr_index A (Category.id_comp (𝟙 X.obj.left))] at h
      rw [h, indexIso_trans_app]
      simp only [indexIso_refl, Iso.refl_hom, NatTrans.id_app]) (by
      intro M N
      have h := ht (𝟙 X) (𝟙 X) M N
      simp only [leftDerivedUpperStarTensorIso_hom] at h
      simp only [leftDerivedUpperStarTensorNatIso_hom]
      dsimp only [Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.postcompose₂, Functor.comp_obj, Functor.id_obj] at h ⊢
      exact h)
  exact hu K N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_projection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : ProperOpenDerived A X) (N : ProperOpenDerived A Y) :
    properOpenProjection A f M N =
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointProjectionMap
          (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)).app M).app N := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_sId_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    (ordinary F A).sId X = conjugateIsoEquiv ((ordinary F A).adj (𝟙 X))
      Adjunction.id ((ordinary F A).pId X).symm := by
  exact (conjugateIsoEquiv_iso_symm Adjunction.id
    ((ordinary F A).adj (𝟙 X)) ((ordinary F A).pId X)).symm

attribute [local irreducible] Calculus.sId

-- Infer the native component type, avoiding conversion through the calculus's category field.
set_option linter.defProp false in
attribute [-instance] CategoryTheory.catToReflQuiver in
private def finite_identity_projection (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ht : OrdinaryTensorComposition F A) (X : Spaces F)
    (K N : ProperOpenDerived A X.obj.left) :=
  identity_projection_normalized (ProperOpenTensor A X.obj.left)
    ((ordinary F A).adj (𝟙 X)) ((ordinary F A).pId X)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A)
      (𝟙 X : X ⟶ X).hom.left) (by
      intro M N
      have h := finite_tensor_identity F A ht X M N
      simp only [leftDerivedUpperStarTensorNatIso_hom] at h
      dsimp only [Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.postcompose₂, Functor.comp_obj, Functor.id_obj] at h
      exact h)
    ((ordinary F A).sId X) (finite_sId_eq F A X)
    (properOpenProjection A (𝟙 X : X ⟶ X).hom.left)
    (finite_projection_eq A (𝟙 X : X ⟶ X).hom.left) K N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_identity_pull_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    (ordinary F A).P (𝟙 X) = ProperOpenPull A (𝟙 X.obj.left) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_identity_push_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    (ordinary F A).S (𝟙 X) = ProperOpenPush A (𝟙 X.obj.left) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_identity_pull_iso_heq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    HEq ((ordinary F A).pId X)
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left) := HEq.rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_identity_iso_heq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    @HEq ((ordinary F A).S (𝟙 X) ≅ 𝟭 (ProperOpenDerived A X.obj.left))
      ((ordinary F A).sId X)
      (ProperOpenPush A (𝟙 X.obj.left) ≅ 𝟭 (ProperOpenDerived A X.obj.left))
      ((ordinary F A).sId X) := HEq.rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_identity_projection_heq (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Spaces F) :
    HEq (properOpenProjection A (𝟙 X : X ⟶ X).hom.left)
      (properOpenProjection A (𝟙 X.obj.left)) := by
  exact dependent_congr_heq
    (fun g : X.obj.left ⟶ X.obj.left ↦ properOpenProjection A g)
    (show (𝟙 X : X ⟶ X).hom.left = 𝟙 X.obj.left from rfl)

set_option linter.defProp false in
attribute [-instance] CategoryTheory.catToReflQuiver in
private def finite_identity_projection_uncurried
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ht : OrdinaryTensorComposition F A) (X : Spaces F)
    (K N : ProperOpenDerived A X.obj.left) :=
  retype_identity_projection (ProperOpenTensor A X.obj.left)
    (U := (ordinary F A).P (𝟙 X)) (V := (ordinary F A).S (𝟙 X))
    (U' := ProperOpenPull A (𝟙 X.obj.left)) (V' := ProperOpenPush A (𝟙 X.obj.left))
    (finite_identity_pull_eq F A X) (finite_identity_push_eq F A X)
    ((ordinary F A).pId X)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left)
    (finite_identity_pull_iso_heq F A X)
    ((ordinary F A).sId X) ((ordinary F A).sId X) (finite_identity_iso_heq F A X)
    (properOpenProjection A (𝟙 X : X ⟶ X).hom.left)
    (properOpenProjection A (𝟙 X.obj.left)) (finite_identity_projection_heq F A X)
    (fun M N ↦ finite_identity_projection F A ht X M N) K N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_pull_assoc
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : ProperOpenDerived A Z) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f (g ≫ h)).hom.app M ≫
      (ProperOpenPull A f).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g h).hom.app M) =
    (indexIso (ProperOpenPull A) (Category.assoc f g h).symm).hom.app M ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (f ≫ g) h).hom.app M ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app
        ((ProperOpenPull A h).obj M) := by
  have ha := leftDerivedUpperStarComp_assoc_app (A := ModuleCat.{u + 1} A) f g h M
  rw [finite_congr_index A (Category.assoc f g h)] at ha
  apply (cancel_epi ((indexIso (ProperOpenPull A) (Category.assoc f g h)).hom.app M)).1
  simp only [← Category.assoc, indexIso_trans_app]
  simpa only [Category.assoc, indexIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] using ha.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_left_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : ProperOpenDerived A Y) :
    (indexIso (ProperOpenPull A) (Category.id_comp f).symm).hom.app M ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X) f).hom.app M ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((ProperOpenPull A f).obj M) = 𝟙 _ := by
  have h := leftDerivedUpperStarComp_id_left_app (A := ModuleCat.{u + 1} A) f M
  rw [finite_congr_index A (Category.id_comp f)] at h
  rw [h, indexIso_trans_app]
  simp only [indexIso_refl, Iso.refl_hom, NatTrans.id_app]

attribute [-instance] CategoryTheory.catToReflQuiver in
private def finite_open_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (ProperOpenShriek A j).prod (𝟭 _) ⋙ Functor.uncurry.obj (ProperOpenTensor A Y) ⟶
      (𝟭 _).prod (ProperOpenPull A j) ⋙ Functor.uncurry.obj (ProperOpenTensor A X) ⋙
        ProperOpenShriek A j :=
  uncurry_open_map (ProperOpenTensor A X) (ProperOpenTensor A Y)
    (ProperOpenShriek A j) (ProperOpenPull A j)
    (derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).inv

attribute [local irreducible] indexIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_pullback_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
    (L : ProperOpenDerived A Y) :
    let e := leftDerivedUpperStarId (ModuleCat.{u + 1} A) X
    let sq := properOpenPullSquareIso A c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)
    let t := Functor.isoWhiskerLeft (ProperOpenPull A c₂.i) e.symm ≪≫ sq
    t.hom.app ((ProperOpenPull A c₂.g).obj L) ≫
      (ProperOpenPull A c₁.i).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g).inv.app L ≫
          (indexIso (ProperOpenPull A) r.hom_g).hom.app L) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₁).hom.app L =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₂).hom.app L := by
  dsimp only
  have hs := normalize_square (ProperOpenDerived A) (ProperOpenPull A)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A))
    c₁.i r.hom c₂.i r.i_hom
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X) (finite_left_unit A c₂.i)
    ((ProperOpenPull A c₂.g).obj L)
  dsimp only [properOpenPullSquareIso, leftDerivedUpperStarSquareIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app] at hs ⊢
  rw [finite_congr_index A (r.i_hom.trans (Category.id_comp c₂.i).symm).symm]
  simp only [Category.assoc] at hs ⊢
  refine ((reassoc_of% hs)
    ((ProperOpenPull A c₁.i).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g).inv.app L ≫
        (indexIso (ProperOpenPull A) r.hom_g).hom.app L) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₁).hom.app L)).trans ?_
  simpa only [leftDerivedUpperStarCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app,
    eqToIso_congrArg_indexIso (ProperOpenPull A) c₁.comm.symm,
    eqToIso_congrArg_indexIso (ProperOpenPull A) c₂.comm.symm, Category.assoc]
    using pull_triangle_transport (ProperOpenDerived A) (ProperOpenPull A)
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A))
      c₁.i r.hom c₂.g c₂.i c₁.g f r.i_hom r.hom_g
      c₁.comm.symm c₂.comm.symm L (finite_pull_assoc A c₁.i r.hom c₂.g L)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_raw_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
    [QuasiCompact c₁.i] [QuasiCompact c₂.i]
    (K : ProperOpenDerived A X) (N : ProperOpenDerived A c₂.Z) :
    let TX := Functor.uncurry.obj (ProperOpenTensor A X)
    let TC := Functor.uncurry.obj (ProperOpenTensor A c₂.Z)
    let J := ProperOpenShriek A c₁.i
    let J' := ProperOpenShriek A c₂.i
    let S := ProperOpenPush A r.hom
    let V := ProperOpenPush A (𝟙 X)
    let g := properOpenMate A c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)
    let sq := properOpenPullSquareIso A c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)
    (finite_open_tensor A c₂.i).app (V.obj K, N) ≫
      J'.map (properOpenProjection A (𝟙 X) K ((ProperOpenPull A c₂.i).obj N)) ≫
      J'.map (V.map (TX.map (Prod.mkHom (𝟙 K) (sq.hom.app N)))) ≫
      g.app (TX.obj (K, (ProperOpenPull A c₁.i).obj ((ProperOpenPull A r.hom).obj N))) =
    TC.map (Prod.mkHom (g.app K) (𝟙 N)) ≫
      properOpenProjection A r.hom (J.obj K) N ≫
      S.map ((finite_open_tensor A c₁.i).app (K, (ProperOpenPull A r.hom).obj N)) := by
  dsimp only
  have h := properOpenProjectionMate A c₁.i (𝟙 X) r.hom c₂.i
    (r.i_hom.trans (Category.id_comp _).symm) K N
  simpa only [finite_open_tensor, uncurry_open_map, Iso.symm_hom, Iso.app_inv,
    uncurry_first (ProperOpenTensor A X), uncurry_first (ProperOpenTensor A c₂.Z),
    uncurry_second (ProperOpenTensor A X), Functor.uncurry_map_app,
    properOpenTensorIso, properOpenMateTensorMap, eqToHom_refl,
    Category.id_comp, Category.comp_id, Functor.uncurry_obj_obj,
    Functor.comp_obj, Functor.prod_obj, Functor.id_obj] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_local (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ht : OrdinaryTensorComposition F A)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    Words.Local (finiteWords F A r) := by
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let TX := Functor.uncurry.obj (ProperOpenTensor A X.obj.left)
  let TB := Functor.uncurry.obj (ProperOpenTensor A c₁.Z)
  let TC := Functor.uncurry.obj (ProperOpenTensor A c₂.Z)
  let J := ProperOpenShriek A c₁.i
  let J' := ProperOpenShriek A c₂.i
  let S := ProperOpenPush A r.hom
  let e := leftDerivedUpperStarId (ModuleCat.{u + 1} A) X.obj.left
  let a := ((ordinary F A).sId X).inv
  let g := properOpenMate A c₁.i (𝟙 X.obj.left) r.hom c₂.i
    (r.i_hom.trans (Category.id_comp _).symm)
  let sq := properOpenPullSquareIso A c₁.i (𝟙 X.obj.left) r.hom c₂.i
    (r.i_hom.trans (Category.id_comp _).symm)
  let t := Functor.isoWhiskerLeft (ProperOpenPull A c₂.i) e.symm ≪≫ sq
  have hm := normalize_mate TX TB TC J J' S
    (ProperOpenPull A c₁.i) (ProperOpenPull A r.hom) (ProperOpenPull A c₂.i)
    (ProperOpenPull A (𝟙 X.obj.left)) (ProperOpenPush A (𝟙 X.obj.left))
    e a g sq (finite_open_tensor A c₁.i) (finite_open_tensor A c₂.i)
    (properOpenProjection A (𝟙 X.obj.left)) (properOpenProjection A r.hom)
    (finite_identity_projection_uncurried F A ht X)
    (finite_raw_mate A c₁ c₂ r)
  have htrans (L : ProperOpenDerived A Y.obj.left) :
      t.hom.app ((ProperOpenPull A c₂.g).obj L) ≫
        (ProperOpenPull A c₁.i).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g).inv.app L ≫
            (indexIso (ProperOpenPull A) r.hom_g).hom.app L) ≫
        (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₁).hom.app L =
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₂).hom.app L := by
    exact finite_pullback_transport A c₁ c₂ r L
  intro K L
  have h := transport_local TX TB TC J J' S
    (ProperOpenPull A c₁.i) (ProperOpenPull A r.hom) (ProperOpenPull A c₂.i)
    (ProperOpenPull A c₂.g) (ProperOpenPull A c₁.g) (ProperOpenPull A f.hom.left)
    (identityNormalize J J' (ProperOpenPush A (𝟙 X.obj.left)) S a g)
    (finite_open_tensor A c₁.i) (finite_open_tensor A c₂.i)
    (properOpenProjection A r.hom) t.hom
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r.hom c₂.g).symm ≪≫
      indexIso (ProperOpenPull A) r.hom_g).hom
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₁).hom
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c₂).hom
    htrans hm K L
  dsimp only [finite_open_tensor, uncurry_open_map, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app] at h
  dsimp only [Words.Local, finiteWords]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    Functor.uncurry_obj_obj] at h ⊢
  dsimp only [TX, TB, TC, J, J', S, a, g] at h
  simpa only [uncurry_first (ProperOpenTensor A c₂.Z),
    uncurry_second (ProperOpenTensor A X.obj.left),
    uncurry_second (ProperOpenTensor A c₁.Z), Functor.uncurry_obj_obj] using h

end FiniteProof

section SystemProof

open WeilConjectures.IntegralSystemRealization

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory instCategoryDerivedCategory
  WeilConjectures.pullbackTensorCalculus WeilConjectures.pullbackTensorSystemComparison
  SemilinearProperOpen.sId Direct.adj

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_pull_assoc
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : System l E Z) :
    (c.pullComp f (g ≫ h)).hom.app M ≫
      (pull l E f).map ((c.pullComp g h).hom.app M) =
    (indexIso (pull l E) (Category.assoc f g h).symm).hom.app M ≫
      (c.pullComp (f ≫ g) h).hom.app M ≫
      (c.pullComp f g).hom.app ((pull l E h).obj M) := by
  exact pull_assoc_app (System l E) (pull l E) c.pullComp f g h
    (integralSystemCompositorAssociativity l E c f g h) M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem indexIso_hom_app {I C D : Type*} [Category C] [Category D]
    (P : I → C ⥤ D) {i j : I} (h : i = j) (M : C) :
    (indexIso P h).hom.app M = eqToHom (congrArg (fun i ↦ (P i).obj M) h) := by
  cases h
  rfl

attribute [local irreducible] indexIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_identity_projection
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E F o)
    (ht : SystemTensorComposition F l E o z.compositors) (X : Spaces F)
    (e : pull l E (𝟙 X.obj.left) ≅ 𝟭 (System l E X.obj.left))
    (he : ∀ M, (indexIso (pull l E)
        (Category.id_comp (𝟙 X.obj.left)).symm).hom.app M ≫
      (z.compositors.pullComp (𝟙 X.obj.left) (𝟙 X.obj.left)).hom.app M ≫
      (pull l E (𝟙 X.obj.left)).map (e.hom.app M) = 𝟙 _)
    (hb : conjugateIsoEquiv (o.direct (𝟙 X.obj.left)).adj Adjunction.id e.symm =
      z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left)
    (K N : System l E X.obj.left) :
    let T := (calculus l E X.obj.left).systemClosed.tensor
    let a := (z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
      SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left).inv
    T.map (Prod.mkHom (a.app K) (𝟙 N)) ≫
      ((properProjection l E o (𝟙 X.obj.left)).app K).app N =
    a.app (T.obj (K, N)) ≫ (Operations.push l E o (𝟙 X.obj.left)).map
      (T.map (Prod.mkHom (𝟙 K) (e.inv.app N))) := by
  dsimp only
  let T := (calculus l E X.obj.left).systemClosed.tensor
  have htt := ht (𝟙 X) (𝟙 X)
  dsimp only [ObjectProperty.FullSubcategory.id_hom,
    ObjectProperty.FullSubcategory.comp_hom, Over.id_left, Over.comp_left] at htt
  have hu (M N : System l E X.obj.left) := tensor_identity_unit_index T
    (fun g : X.obj.left ⟶ X.obj.left ↦ pull l E g)
    (fun g ↦ WeilConjectures.pullbackTensorSystemComparison l E g)
    (Category.id_comp (𝟙 X.obj.left)) e
    (z.compositors.pullComp (𝟙 X.obj.left) (𝟙 X.obj.left)) he
    htt M N
  exact identity_projection_uncurried_normalized T (o.direct (𝟙 X.obj.left)).adj e
    (WeilConjectures.pullbackTensorSystemComparison l E (𝟙 X.obj.left)) hu
    (z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
      SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left)
    hb.symm (fun M N ↦ ((properProjection l E o (𝟙 X.obj.left)).app M).app N)
    (fun M N ↦ rfl) K N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_left_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {X : Scheme.{u}} (e : pull l E (𝟙 X) ≅ 𝟭 (System l E X))
    (he : ∀ M, (indexIso (pull l E) (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c.pullComp (𝟙 X) (𝟙 X)).hom.app M ≫
      (pull l E (𝟙 X)).map (e.hom.app M) = 𝟙 _)
    {Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E Y) :
    (indexIso (pull l E) (Category.id_comp f).symm).hom.app M ≫
      (c.pullComp (𝟙 X) f).hom.app M ≫ e.hom.app ((pull l E f).obj M) = 𝟙 _ := by
  exact pull_left_unit (System l E) (pull l E) c.pullComp e he f M
    (system_pull_assoc l E c (𝟙 X) (𝟙 X) f M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_congr_index
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    eqToIso (congrArg (pull l E) h) = indexIso (pull l E) h := by
  exact eqToIso_congrArg_indexIso (pull l E) h

attribute [-instance] CategoryTheory.catToReflQuiver in
-- Rewrite the isomorphism before taking components: reducing equality transport
-- between derived functor values directly is expensive in the kernel.
private theorem system_square_index
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    c.square l E k r p i h = (c.pullComp r i).symm ≪≫
      indexIso (pull l E) h.symm ≪≫ c.pullComp k p := by
  exact congrArg (fun t ↦ (c.pullComp r i).symm ≪≫ t ≪≫ c.pullComp k p)
    (system_congr_index l E h.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_square_hom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) (M : System l E Z) :
    (c.square l E k r p i h).hom.app M =
      (c.pullComp r i).inv.app M ≫
        (indexIso (pull l E) h.symm).hom.app M ≫ (c.pullComp k p).hom.app M := by
  rw [system_square_index l E c k r p i h]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_normalize_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {X : Scheme.{u}} (e : pull l E (𝟙 X) ≅ 𝟭 (System l E X))
    (he : ∀ M, (indexIso (pull l E) (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c.pullComp (𝟙 X) (𝟙 X)).hom.app M ≫
      (pull l E (𝟙 X)).map (e.hom.app M) = 𝟙 _)
    {B C : Scheme.{u}} (k : X ⟶ B) (v : B ⟶ C) (i : X ⟶ C) (h : k ≫ v = i)
    (M : System l E C) :
    e.inv.app ((pull l E i).obj M) ≫ (c.pullComp (𝟙 X) i).inv.app M ≫
      (indexIso (pull l E) (h.trans (Category.id_comp i).symm).symm).hom.app M ≫
      (c.pullComp k v).hom.app M =
      (indexIso (pull l E) h.symm).hom.app M ≫ (c.pullComp k v).hom.app M := by
  exact normalize_square (System l E) (pull l E) c.pullComp k v i h e
    (system_left_unit l E c e he i) M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_normalized_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {X : Scheme.{u}} (e : pull l E (𝟙 X) ≅ 𝟭 (System l E X))
    (he : ∀ M, (indexIso (pull l E) (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c.pullComp (𝟙 X) (𝟙 X)).hom.app M ≫
      (pull l E (𝟙 X)).map (e.hom.app M) = 𝟙 _)
    {B C : Scheme.{u}} (k : X ⟶ B) (v : B ⟶ C) (i : X ⟶ C) (h : k ≫ v = i)
    (M : System l E C) :
    (Functor.isoWhiskerLeft (pull l E i) e.symm ≪≫
      c.square l E k (𝟙 X) v i (h.trans (Category.id_comp i).symm)).hom.app M =
      (indexIso (pull l E) h.symm).hom.app M ≫ (c.pullComp k v).hom.app M := by
  have hs := system_normalize_square l E c e he k v i h M
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, NatTrans.comp_app]
  rw [system_square_hom l E c k (𝟙 X) v i]
  simpa only [Category.assoc] using hs

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_triangle_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {X B C Y : Scheme.{u}} (k : X ⟶ B) (v : B ⟶ C) (p : C ⟶ Y)
    (i : X ⟶ C) (q : B ⟶ Y) (f : X ⟶ Y)
    (hi : k ≫ v = i) (hq : v ≫ p = q) (hf : k ≫ q = f) (hf' : i ≫ p = f)
    (M : System l E Y) :
    (indexIso (pull l E) hi.symm).hom.app ((pull l E p).obj M) ≫
      (c.pullComp k v).hom.app ((pull l E p).obj M) ≫
      (pull l E k).map ((c.pullComp v p).inv.app M ≫
        (indexIso (pull l E) hq).hom.app M) ≫
      (c.pullComp k q).inv.app M ≫ (indexIso (pull l E) hf).hom.app M =
      (c.pullComp i p).inv.app M ≫ (indexIso (pull l E) hf').hom.app M := by
  exact pull_triangle_transport (System l E) (pull l E) c.pullComp
    k v p i q f hi hq hf hf' M (system_pull_assoc l E c k v p M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_pullback_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {o : Operations l E} (c : Compositors l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c₁ c₂ : Compactification f) (r : c₁.Refinement c₂)
    (e : pull l E (𝟙 X) ≅ 𝟭 (System l E X))
    (he : ∀ M, (indexIso (pull l E) (Category.id_comp (𝟙 X)).symm).hom.app M ≫
      (c.pullComp (𝟙 X) (𝟙 X)).hom.app M ≫
      (pull l E (𝟙 X)).map (e.hom.app M) = 𝟙 _) (L : System l E Y) :
    let sq := c.square l E c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)
    let t := Functor.isoWhiskerLeft (pull l E c₂.i) e.symm ≪≫ sq
    let b := (c.pullComp c₁.i c₁.g).symm ≪≫ indexIso (pull l E) c₁.comm.symm
    let b' := (c.pullComp c₂.i c₂.g).symm ≪≫ indexIso (pull l E) c₂.comm.symm
    let v := (c.pullComp r.hom c₂.g).symm ≪≫ indexIso (pull l E) r.hom_g
    t.hom.app ((pull l E c₂.g).obj L) ≫ (pull l E c₁.i).map (v.hom.app L) ≫
      b.hom.app L = b'.hom.app L := by
  dsimp only
  have hs := system_normalized_square l E c e he c₁.i r.hom c₂.i r.i_hom
    ((pull l E c₂.g).obj L)
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hs ⊢
  rw [hs]
  simpa only [Category.assoc] using
    system_triangle_transport l E c c₁.i r.hom c₂.g c₂.i c₁.g f
      r.i_hom r.hom_g c₁.comm.symm c₂.comm.symm L

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem system_local (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (z : Realizations l E F o)
    (ht : SystemTensorComposition F l E o z.compositors)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    Words.Local (WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords
      l E F o z r) := by
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let : X.obj.left.Over (Spec (.of F.k)) := ⟨X.obj.hom⟩
  let : c₁.Z.Over (Spec (.of F.k)) := ⟨c₁.g ≫ Y.obj.hom⟩
  let : c₂.Z.Over (Spec (.of F.k)) := ⟨c₂.g ≫ Y.obj.hom⟩
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  let : LocallyOfFiniteType (X.obj.left ↘ Spec (.of F.k)) := X.property.1
  let : QuasiCompact (X.obj.left ↘ Spec (.of F.k)) := X.property.2
  let : LocallyOfFiniteType (c₁.Z ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (c₁.g ≫ Y.obj.hom))
  let : QuasiCompact (c₁.Z ↘ Spec (.of F.k)) :=
    inferInstanceAs (QuasiCompact (c₁.g ≫ Y.obj.hom))
  let : LocallyOfFiniteType (c₂.Z ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (c₂.g ≫ Y.obj.hom))
  let : QuasiCompact (c₂.Z ↘ Spec (.of F.k)) :=
    inferInstanceAs (QuasiCompact (c₂.g ≫ Y.obj.hom))
  let : c₁.i.IsOver (Spec (.of F.k)) := ⟨by
    change c₁.i ≫ (c₁.g ≫ Y.obj.hom) = X.obj.hom
    rw [← Category.assoc, ← c₁.comm]
    exact f.hom.w⟩
  let : c₂.i.IsOver (Spec (.of F.k)) := ⟨by
    change c₂.i ≫ (c₂.g ≫ Y.obj.hom) = X.obj.hom
    rw [← Category.assoc, ← c₂.comm]
    exact f.hom.w⟩
  let : r.hom.IsOver (Spec (.of F.k)) := ⟨by
    change r.hom ≫ (c₂.g ≫ Y.obj.hom) = c₁.g ≫ Y.obj.hom
    rw [← Category.assoc, r.hom_g]⟩
  obtain ⟨e, he₀, hb⟩ := systemPushIdentityPullUnit l E o z.compositors
    z.canonicalBridge X.obj.left
  have he := pull_unit_app (System l E) (pull l E) z.compositors.pullComp e he₀
  let TX := (calculus l E X.obj.left).systemClosed.tensor
  let TB := (calculus l E c₁.Z).systemClosed.tensor
  let TC := (calculus l E c₂.Z).systemClosed.tensor
  let J := Operations.shriek l E o c₁.i
  let J' := Operations.shriek l E o c₂.i
  let S := Operations.push l E o r.hom
  let a := (z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
    SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left).inv
  let g := z.properOpen.gamma c₁.i (𝟙 X.obj.left) r.hom c₂.i
    (r.i_hom.trans (Category.id_comp _).symm)
  let sq := z.compositors.square l E c₁.i (𝟙 X.obj.left) r.hom c₂.i
    (r.i_hom.trans (Category.id_comp _).symm)
  let t := Functor.isoWhiskerLeft (pull l E c₂.i) e.symm ≪≫ sq
  have hm := normalize_mate TX TB TC J J' S
    (pull l E c₁.i) (pull l E r.hom) (pull l E c₂.i)
    (pull l E (𝟙 X.obj.left)) (Operations.push l E o (𝟙 X.obj.left))
    e a g sq (z.openComparisons.projection c₁.i).hom (z.openComparisons.projection c₂.i).hom
    (fun K N ↦ ((properProjection l E o (𝟙 X.obj.left)).app K).app N)
    (fun K N ↦ ((properProjection l E o r.hom).app K).app N)
    (system_identity_projection F l E o z ht X e he hb)
    (properOpenProjectionMateSystems F l hl E o z c₁.i (𝟙 X.obj.left) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm))
  let b := (z.compositors.pullComp c₁.i c₁.g).symm ≪≫
    indexIso (pull l E) c₁.comm.symm
  let b' := (z.compositors.pullComp c₂.i c₂.g).symm ≪≫
    indexIso (pull l E) c₂.comm.symm
  let v := (z.compositors.pullComp r.hom c₂.g).symm ≪≫ indexIso (pull l E) r.hom_g
  have htrans := system_pullback_transport l E z.compositors c₁ c₂ r e he
  dsimp only [Words.Local,
    WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords]
  intro K L
  have h := transport_local TX TB TC J J' S
    (pull l E c₁.i) (pull l E r.hom) (pull l E c₂.i)
    (pull l E c₂.g) (pull l E c₁.g) (pull l E f.hom.left)
    (identityNormalize J J' (Operations.push l E o (𝟙 X.obj.left)) S a g)
    (z.openComparisons.projection c₁.i).hom (z.openComparisons.projection c₂.i).hom
    (fun M N ↦ ((properProjection l E o r.hom).app M).app N)
    t.hom v.hom b.hom b'.hom htrans hm K L
  dsimp only [b, b', v, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at h
  simp only [indexIso_hom_app (pull l E) c₁.comm.symm L,
    indexIso_hom_app (pull l E) c₂.comm.symm L,
    indexIso_hom_app (pull l E) r.hom_g L] at h
  dsimp only [TX, TB, TC, J, J', S, a, g] at h
  exact h

end SystemProof

/-- Stacks 0F7B and 0B56, the local part of the refinement calculation.
(blueprint: lem-sf-refinement-projection-local-tensor).

Proof: Apply properOpenProjectionMate to (j1,id,u,j2) with N=P_p2 L. Normalize the
identity projection by its adjunction-conjugate identity comparison. In the system case,
choose the pullback identity comparison of systemPushIdentityPullUnit: its conjugate
is exactly the canonical bridge followed by the sectionwise direct-image identity.
The normalized two-identity unit law and compositor associativity give the left unit
law for every map, by specializing associativity to (id,id,f) and cancelling the
invertible compositor. The identity specialization of ambient tensor composition
then makes the pullback identity comparison tensor compatible; cancel the invertible
tensor comparison. The projection conjugation formula now identifies the normalized
identity direct-image projection with the identity. Naturality of the
open tensor map moves that comparison to its first input. Pullback unit coherence and
associativity identify the square comparison followed by the first compactification
comparison with the second compactification comparison. Naturality of gamma moves
this final transport through gamma. This proves the local equation. The same steps
inside the simultaneous system category use the canonical bridge and its section
normalization, so all transitions are retained. No projection or gamma is inverted.
-/
theorem refinementProjectionLocalTensor
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    {X Y : Spaces F} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c₁ c₂ : Compactification f.hom.left) (r : c₁.Refinement c₂) :
    Words.Local (finiteWords F
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o),
      Words.Local (WeilConjectures.IntegralSystemRealization.RefinementProjection.systemWords
        l E F o z r) := by
  constructor
  · exact finite_local F _ (ambientProperOpenPasting F l _hl E n).2.1 c₁ c₂ r
  · intro o z
    exact system_local F l _hl E o z
      ((ambientProperOpenPasting F l _hl E n).2.2.2 o z.compositors) c₁ c₂ r

end AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection
