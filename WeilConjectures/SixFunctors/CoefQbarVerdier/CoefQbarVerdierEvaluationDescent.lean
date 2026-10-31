/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierTensorInclusion
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteEvaluationStage
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteOmegaStageCoherence

/-! # The constructed common-stage dualizing object and evaluation

Source: thm-coef-qbar-verdier, proof steps 4--5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite
attribute [local implicit_reducible] StageSystem.ι StageSystem.opposite
  StageSystem.Morphism.functor StageSystem.contravariantMorphism
  StageSystem.pairUnopFunctor StageSystem.transportContravariantMorphism

private theorem q3_dinatural_comp
    {C : Type*} [Category C] (T : C × C ⥤ C) (d : Cᵒᵖ ⥤ C) (w : C)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    {K M N : C} (f : K ⟶ M) (g : M ⟶ N)
    (hf : T.map (Prod.mkHom f (𝟙 _)) ≫ ev M =
      T.map (Prod.mkHom (𝟙 K) (d.map f.op)) ≫ ev K)
    (hg : T.map (Prod.mkHom g (𝟙 _)) ≫ ev N =
      T.map (Prod.mkHom (𝟙 M) (d.map g.op)) ≫ ev M) :
    T.map (Prod.mkHom (f ≫ g) (𝟙 _)) ≫ ev N =
      T.map (Prod.mkHom (𝟙 K) (d.map (f ≫ g).op)) ≫ ev K := by
  calc
    _ = T.map (Prod.mkHom f (𝟙 _)) ≫
        T.map (Prod.mkHom g (𝟙 _)) ≫ ev N := by
      rw [← T.map_comp_assoc]
      simp
    _ = T.map (Prod.mkHom f (𝟙 _)) ≫
        T.map (Prod.mkHom (𝟙 M) (d.map g.op)) ≫ ev M := by rw [hg]
    _ = T.map (Prod.mkHom (𝟙 K) (d.map g.op)) ≫
        T.map (Prod.mkHom f (𝟙 _)) ≫ ev M := by
      simp only [← T.map_comp_assoc]
      congr 2
      simp
    _ = T.map (Prod.mkHom (𝟙 K) (d.map g.op)) ≫
        T.map (Prod.mkHom (𝟙 K) (d.map f.op)) ≫ ev K := by rw [hf]
    _ = _ := by
      simp [← T.map_comp_assoc, ← d.map_comp, ← op_comp]

private theorem q3_dinatural_inv
    {C : Type*} [Category C] (T : C × C ⥤ C) (d : Cᵒᵖ ⥤ C) (w : C)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    {K M : C} (a : K ≅ M)
    (ha : T.map (Prod.mkHom a.hom (𝟙 _)) ≫ ev M =
      T.map (Prod.mkHom (𝟙 K) (d.map a.hom.op)) ≫ ev K) :
    T.map (Prod.mkHom a.inv (𝟙 _)) ≫ ev K =
      T.map (Prod.mkHom (𝟙 M) (d.map a.inv.op)) ≫ ev M := by
  apply (cancel_epi (T.mapIso (Iso.prod a (Iso.refl _))).hom).mp
  dsimp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  calc
    _ = ev K := by simp [← T.map_comp_assoc]
    _ = T.map (Prod.mkHom (𝟙 K) (d.map a.inv.op)) ≫
        T.map (Prod.mkHom (𝟙 K) (d.map a.hom.op)) ≫ ev K := by
      simp [← T.map_comp_assoc, ← d.map_comp, ← op_comp]
    _ = T.map (Prod.mkHom (𝟙 K) (d.map a.inv.op)) ≫
        T.map (Prod.mkHom a.hom (𝟙 _)) ≫ ev M := by rw [← ha]
    _ = _ := by
      simp only [← T.map_comp_assoc]
      congr 2
      simp

private theorem q3_included_evaluation_natural
    {C : Type*} [Category C] {B : Type*} [Category B]
    (U : C × C ⥤ C) (T : B × B ⥤ B) (J : C ⥤ B)
    (d : Cᵒᵖ ⥤ C) (e : Bᵒᵖ ⥤ B) (w : C) (z : B)
    (ev : ∀ K, U.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, T.obj (K, e.obj (op K)) ⟶ z)
    (b : d ⋙ J ≅ J.op ⋙ e) (o : J.obj w ≅ z)
    (t : ∀ K P, J.obj (U.obj (K, P)) ≅ T.obj (J.obj K, J.obj P))
    (hev : ∀ {K M} (f : K ⟶ M), U.map (Prod.mkHom f (𝟙 _)) ≫ ev M =
      U.map (Prod.mkHom (𝟙 K) (d.map f.op)) ≫ ev K)
    (ht : ∀ {K K' P P'} (f : K ⟶ K') (g : P ⟶ P'),
      J.map (U.map (Prod.mkHom f g)) ≫ (t K' P').hom =
        (t K P).hom ≫ T.map (Prod.mkHom (J.map f) (J.map g)))
    (he : ∀ K, (t K (d.obj (op K))).hom ≫
      T.map (Prod.mkHom (𝟙 (J.obj K)) (b.hom.app (op K))) ≫ ew (J.obj K) =
        J.map (ev K) ≫ o.hom)
    {K M : C} (f : K ⟶ M) :
    T.map (Prod.mkHom (J.map f) (𝟙 _)) ≫ ew (J.obj M) =
      T.map (Prod.mkHom (𝟙 _) (e.map (J.map f).op)) ≫ ew (J.obj K) := by
  apply (cancel_epi ((t K (d.obj (op M))) ≪≫
    T.mapIso (Iso.prod (Iso.refl _) (b.app (op M)))).hom).mp
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app]
  have hb := b.hom.naturality f.op
  dsimp only [Functor.comp_map, Functor.op_map] at hb
  change J.map (d.map f.op) ≫ b.hom.app (op K) =
    b.hom.app (op M) ≫ e.map (J.map f).op at hb
  calc
    _ = (t K (d.obj (op M))).hom ≫
        T.map (Prod.mkHom (J.map f) (𝟙 _)) ≫
        T.map (Prod.mkHom (𝟙 _) (b.hom.app (op M))) ≫ ew (J.obj M) := by
      simp only [Category.assoc, ← T.map_comp_assoc]
      congr 2
      simp
    _ = J.map (U.map (Prod.mkHom f (𝟙 _))) ≫
        (t M (d.obj (op M))).hom ≫
        T.map (Prod.mkHom (𝟙 _) (b.hom.app (op M))) ≫ ew (J.obj M) := by
      rw [reassoc_of% (ht f (𝟙 _)), J.map_id]
    _ = J.map (U.map (Prod.mkHom f (𝟙 _))) ≫ J.map (ev M) ≫ o.hom := by rw [he]
    _ = J.map (U.map (Prod.mkHom (𝟙 K) (d.map f.op))) ≫
        J.map (ev K) ≫ o.hom := by rw [← J.map_comp_assoc, hev, J.map_comp_assoc]
    _ = J.map (U.map (Prod.mkHom (𝟙 K) (d.map f.op))) ≫
        (t K (d.obj (op K))).hom ≫
        T.map (Prod.mkHom (𝟙 _) (b.hom.app (op K))) ≫ ew (J.obj K) := by rw [he]
    _ = (t K (d.obj (op M))).hom ≫
        T.map (Prod.mkHom (𝟙 _) (J.map (d.map f.op))) ≫
        T.map (Prod.mkHom (𝟙 _) (b.hom.app (op K))) ≫ ew (J.obj K) := by
      rw [reassoc_of% (ht (𝟙 K) (d.map f.op)), J.map_id]
    _ = _ := by
      simp only [Category.assoc, ← T.map_comp_assoc, prod_comp, Category.id_comp]
      rw [hb]

private theorem q3_evaluation_transition_paste
    {C : Type*} [Category C] {B : Type*} [Category B] {A : Type*} [Category A]
    (U : C × C ⥤ C) (V : B × B ⥤ B) (T : A × A ⥤ A)
    (F : C ⥤ B) (J : C ⥤ A) (H : B ⥤ A)
    (d : Cᵒᵖ ⥤ C) (e : Bᵒᵖ ⥤ B) (q : Aᵒᵖ ⥤ A)
    (w : C) (z : B) (a : A)
    (ev : ∀ K, U.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, V.obj (K, e.obj (op K)) ⟶ z)
    (ea : ∀ K, T.obj (K, q.obj (op K)) ⟶ a)
    (s : F ⋙ H ≅ J) (b : d ⋙ F ≅ F.op ⋙ e) (o : F.obj w ≅ z)
    (c : d ⋙ J ≅ J.op ⋙ q) (c' : e ⋙ H ≅ H.op ⋙ q)
    (r : J.obj w ≅ a) (r' : H.obj z ≅ a)
    (t : U ⋙ F ≅ F.prod F ⋙ V)
    (j : ∀ K P, J.obj (U.obj (K, P)) ≅ T.obj (J.obj K, J.obj P))
    (h : ∀ K P, H.obj (V.obj (K, P)) ≅ T.obj (H.obj K, H.obj P))
    (hn : ∀ {K K' P P'} (f : K ⟶ K') (g : P ⟶ P'),
      H.map (V.map (Prod.mkHom f g)) ≫ (h K' P').hom =
        (h K P).hom ≫ T.map (Prod.mkHom (H.map f) (H.map g)))
    (ht : ∀ K P, H.map (t.hom.app (K, P)) ≫ (h (F.obj K) (F.obj P)).hom ≫
      T.map (Prod.mkHom (s.hom.app K) (s.hom.app P)) =
        s.hom.app (U.obj (K, P)) ≫ (j K P).hom)
    (hc : ∀ K, H.map (b.hom.app (op K)) ≫ c'.hom.app (op (F.obj K)) ≫
      q.map (s.inv.app K).op = s.hom.app (d.obj (op K)) ≫ c.hom.app (op K))
    (ho : H.map o.hom ≫ r'.hom = s.hom.app w ≫ r.hom)
    (he : ∀ K, V.map (Prod.mkHom (𝟙 (F.obj K)) (b.hom.app (op K))) ≫ ew (F.obj K) =
      t.inv.app (K, d.obj (op K)) ≫ F.map (ev K) ≫ o.hom)
    (hj : ∀ K, (j K (d.obj (op K))).hom ≫
      T.map (Prod.mkHom (𝟙 (J.obj K)) (c.hom.app (op K))) ≫ ea (J.obj K) =
        J.map (ev K) ≫ r.hom)
    (hh : ∀ K, (h K (e.obj (op K))).hom ≫
      T.map (Prod.mkHom (𝟙 (H.obj K)) (c'.hom.app (op K))) ≫ ea (H.obj K) =
        H.map (ew K) ≫ r'.hom)
    (K : C) :
    T.map (Prod.mkHom (s.hom.app K) (𝟙 _)) ≫ ea (J.obj K) =
      T.map (Prod.mkHom (𝟙 _) (q.map (s.hom.app K).op)) ≫ ea (H.obj (F.obj K)) := by
  simp only [Functor.comp_obj, Functor.op_obj, unop_op] at hn he
  let p := H.mapIso (t.app (K, d.obj (op K))) ≪≫ h (F.obj K) (F.obj (d.obj (op K))) ≪≫
    T.mapIso (Iso.prod (Iso.refl _) (s.app (d.obj (op K)) ≪≫ c.app (op K)))
  apply (cancel_epi p.hom).mp
  dsimp only [p, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
    Iso.app]
  calc
    _ = H.map (t.hom.app (K, d.obj (op K))) ≫
        (h (F.obj K) (F.obj (d.obj (op K)))).hom ≫
        T.map (Prod.mkHom (s.hom.app K) (s.hom.app (d.obj (op K)))) ≫
        T.map (Prod.mkHom (𝟙 _) (c.hom.app (op K))) ≫ ea (J.obj K) := by
      simp only [Category.assoc, ← T.map_comp_assoc]
      congr 3
      simp
    _ = s.hom.app (U.obj (K, d.obj (op K))) ≫
        (j K (d.obj (op K))).hom ≫
        T.map (Prod.mkHom (𝟙 _) (c.hom.app (op K))) ≫ ea (J.obj K) := by
      rw [reassoc_of% (ht K (d.obj (op K)))]
    _ = s.hom.app (U.obj (K, d.obj (op K))) ≫ J.map (ev K) ≫ r.hom := by rw [hj]
    _ = H.map (F.map (ev K)) ≫ H.map o.hom ≫ r'.hom := by
      rw [ho, ← s.hom.naturality_assoc]
      rfl
    _ = H.map (t.hom.app (K, d.obj (op K))) ≫
        H.map (V.map (Prod.mkHom (𝟙 (F.obj K)) (b.hom.app (op K)))) ≫
        H.map (ew (F.obj K)) ≫ r'.hom := by
      simp only [← H.map_comp_assoc, he, Iso.hom_inv_id_app_assoc]
    _ = H.map (t.hom.app (K, d.obj (op K))) ≫
        (h (F.obj K) (F.obj (d.obj (op K)))).hom ≫
        T.map (Prod.mkHom (𝟙 _) (H.map (b.hom.app (op K)))) ≫
        T.map (Prod.mkHom (𝟙 _) (c'.hom.app (op (F.obj K)))) ≫
        ea (H.obj (F.obj K)) := by
      have hn' := hn (𝟙 (F.obj K)) (b.hom.app (op K))
      change H.map (V.map (Prod.mkHom (𝟙 (F.obj K)) (b.hom.app (op K)))) ≫
        (h (F.obj K) (e.obj (op (F.obj K)))).hom =
        (h (F.obj K) (F.obj (d.obj (op K)))).hom ≫
          T.map (Prod.mkHom (H.map (𝟙 (F.obj K)))
            (H.map (b.hom.app (op K)))) at hn'
      rw [← hh, reassoc_of% hn', H.map_id]
    _ = _ := by
      have hc' := congrArg (fun f ↦ f ≫ q.map (s.hom.app K).op) (hc K)
      simp only [Category.assoc, ← q.map_comp, ← op_comp,
        Iso.hom_inv_id_app, op_id] at hc'
      erw [q.map_id, Category.comp_id] at hc'
      simp only [Category.assoc, ← T.map_comp_assoc, prod_comp, Category.id_comp]
      rw [hc']

private theorem q3_transIso_tower
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    {i j k : I} (h : i ≤ j) (g : j ≤ k) (W : C i) :
    (S.ι k).map ((S.assoc h g).hom.app W) ≫ (S.transIso (h.trans g)).hom.app W =
      (S.transIso g).hom.app ((S.T h).obj W) ≫ (S.transIso h).hom.app W := by
  rw [StageSystem.transIso_hom_app, StageSystem.transIso_hom_app,
    StageSystem.transIso_hom_app,
    BilinearCoefficientDescent.isoToStage_inv_eq (S := S) ⟨i, W⟩ h g]
  dsimp only [StageSystem.isoToStage]
  rw [StageSystem.ι_map_eq le_rfl, StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom k _ _)
  exact S.cocycle h g (le_refl k) W

private theorem q3_omega_from_base
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    (W : ∀ i, C i) (o : ∀ {i j}, (h : i ≤ j) → (S.T h).obj (W i) ≅ W j)
    (ht : ∀ {i j k} (h : i ≤ j) (g : j ≤ k),
      (S.T g).map (o h).hom ≫ (o g).hom = (S.assoc h g).hom.app (W i) ≫
        (o (h.trans g)).hom)
    (b : I) (hb : ∀ i, b ≤ i) {i j : I} (h : i ≤ j) :
    (S.ι j).map (o h).hom ≫
        ((S.ι j).map (o (hb j)).inv ≫ (S.transIso (hb j)).hom.app (W b)) =
      (S.transIso h).hom.app (W i) ≫
        ((S.ι i).map (o (hb i)).inv ≫ (S.transIso (hb i)).hom.app (W b)) := by
  have hh : (o h).hom ≫ (o (hb j)).inv =
      (S.T h).map (o (hb i)).inv ≫ (S.assoc (hb i) h).hom.app (W b) := by
    apply (cancel_epi ((S.T h).mapIso (o (hb i)) ).hom).mp
    dsimp only [Functor.mapIso_hom]
    rw [← Category.assoc, ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← (S.ι j).map_comp_assoc, hh, (S.ι j).map_comp_assoc,
    q3_transIso_tower S (hb i) h (W b)]
  rw [← Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ (S.transIso (hb i)).hom.app (W b))
    ((S.transIso h).hom.naturality (o (hb i)).inv)

private theorem q3_contravariant_transition
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    (F : S.opposite.Morphism S) {i j : I} (h : i ≤ j) (K : C i) :
    (S.ι j).map ((F.β h).hom.app (op K)) ≫
        (StageSystem.contravariantComparison S F j).hom.app (op ((S.T h).obj K)) ≫
        (S.pairUnopFunctor ⋙ F.functor).map ((S.transIso h).inv.app K).op =
      (S.transIso h).hom.app ((F.Φ i).obj (op K)) ≫
        (StageSystem.contravariantComparison S F i).hom.app (op K) := by
  unfold StageSystem.contravariantComparison
  dsimp only [NatIso.ofComponents_hom_app, Iso.refl_hom]
  erw [Category.id_comp, Category.comp_id]
  change (S.ι j).map ((F.β h).hom.app (op K)) ≫
    F.functor.map (S.opPairHom ((S.transIso h).inv.app K)) = _
  change (S.ι j).map ((F.β h).hom.app (op K)) ≫
    F.functor.map (StageSystem.PairCategory.mkHom (S := S.opposite)
      (X := ⟨j, op ((S.T h).obj K)⟩) (Y := ⟨i, op K⟩) j le_rfl h
      (((S.assoc h le_rfl).inv.app K).op)) = _
  rw [F.functor_map_mkHom, StageSystem.ι_map_eq le_rfl,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  change StageSystem.PairCategory.mkHom (S := S)
    (X := ⟨j, (S.T h).obj ((F.Φ i).obj (op K))⟩)
    (Y := ⟨i, (F.Φ i).obj (op K)⟩) j le_rfl h
    ((S.T (le_rfl : j ≤ j)).map ((F.β h).hom.app (op K)) ≫
      ((F.β le_rfl).hom.app (op ((S.T h).obj K)) ≫
        (F.Φ j).map ((S.assoc h le_rfl).inv.app K).op ≫
          (F.β h).inv.app (op K))) = _
  have hc := F.coh h (le_rfl : j ≤ j) (op K)
  change (S.T (le_rfl : j ≤ j)).map ((F.β h).hom.app (op K)) ≫
      (F.β (le_rfl : j ≤ j)).hom.app (op ((S.T h).obj K)) ≫
        (F.Φ j).map ((S.assoc h (le_rfl : j ≤ j)).inv.app K).op =
    (S.assoc h (le_rfl : j ≤ j)).hom.app ((F.Φ i).obj (op K)) ≫
      (F.β h).hom.app (op K) at hc
  rw [← Category.assoc] at hc
  rw [← Category.assoc, ← Category.assoc, hc]
  rw [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rfl

private theorem q3_transport_phi
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    {S T : StageSystem C} (p : S = T) (F : T.opposite.Morphism T) (i : I) :
    (StageSystem.transportContravariantMorphism p F).Φ i = F.Φ i := by
  subst T
  rfl

private theorem q3_transported_contravariant_transition
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    (S T : StageSystem C) (p : S = T) (d : ∀ i, (C i)ᵒᵖ ⥤ C i)
    (b : ∀ {i j}, (h : i ≤ j) → d i ⋙ T.T h ≅ (T.T h).op ⋙ d j)
    (hc : ∀ {i j k} (h : i ≤ j) (g : j ≤ k) (K : C i),
      (T.T g).map ((b h).hom.app (op K)) ≫
          (b g).hom.app (op ((T.T h).obj K)) =
        (T.assoc h g).hom.app ((d i).obj (op K)) ≫
          (b (h.trans g)).hom.app (op K) ≫
            (d k).map ((T.assoc h g).hom.app K).op)
    {i j : I} (h : i ≤ j) (K : C i) :
    let F := StageSystem.contravariantMorphism T d b hc
    let M := StageSystem.transportContravariantMorphism p F
    let D := S.pairUnopFunctor ⋙ M.functor
    let c := fun i ↦ eqToIso (congrArg (fun e ↦ e ⋙ S.ι i)
      (q3_transport_phi p F i).symm) ≪≫ StageSystem.contravariantComparison S M i
    let t := eqToIso (congrArg (fun R : StageSystem C ↦ R.T h) p)
    (S.ι j).map (t.hom.app ((d i).obj (op K)) ≫ (b h).hom.app (op K) ≫
        (d j).map (t.hom.app K).op) ≫
        (c j).hom.app (op ((S.T h).obj K)) ≫ D.map ((S.transIso h).inv.app K).op =
      (S.transIso h).hom.app ((d i).obj (op K)) ≫ (c i).hom.app (op K) := by
  subst T
  dsimp only [StageSystem.transportContravariantMorphism, q3_transport_phi]
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, op_id,
    Category.id_comp, Iso.trans_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hh := q3_contravariant_transition S
    (StageSystem.contravariantMorphism S d b hc) h K
  unfold StageSystem.contravariantComparison at hh ⊢
  dsimp only [NatIso.ofComponents_hom_app, Iso.refl_hom] at hh ⊢
  erw [Category.id_comp, Category.comp_id] at hh
  erw [Category.id_comp, Category.comp_id]
  exact hh

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  ScalarLocalization.category sfRationalConstructibleLocalization
  sfRationalScalarExtension rationalDerivedTensor rationalTensorScalarComparison
  HasDerivedCategory.standard integralCoefficientLinear
attribute [local implicit_reducible] Stage
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- Omega is the included dualizing object at the base coefficient field. -/
def descendedOmega (F : Finite D l hl Ω X) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (inclusion (Padic.finiteCoefficientBase l Ω)).obj
    ((sfRationalConstructibleLocalization l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)) X).obj
        (F.omega (Padic.finiteCoefficientBase l Ω)).omega)

/-- The normalized finite u maps identify every finite omega with the base object. -/
def descendedOmegaComparison (F : Finite D l hl Ω X) (E : Index l Ω) :
    (inclusion E).obj ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega) ≅ descendedOmega D l hl Ω X F := by
  let O := Padic.finiteCoefficientBase l Ω
  have h : O ≤ E := show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le
  exact (inclusion E).mapIso (F.scalar O E h).omega.symm ≪≫
    (inclusionTransition l Ω X O E h).app _

/-- Compare the finite tensor with the actual tensor of the included object and dual. -/
def descendedTensorComparison (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) (K : Stage l Ω X E) :
    (inclusion E).obj ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).obj
      (K, (F.datum E).dual.obj (op K))) ≅
    (CoefQbarTensor D l hl Ω X).obj
      ((inclusion E).obj K, (descendedDual D l hl Ω X F hF).obj (op ((inclusion E).obj K))) :=
  tensorInclusion D l hl Ω X E K ((F.datum E).dual.obj (op K)) ≪≫
    (CoefQbarTensor D l hl Ω X).mapIso
      (Iso.prod (Iso.refl _) ((descendedComparison D l hl Ω X F hF E).app (op K)))

/-- Evaluation is the included finite evaluation at the object's own stage,
transported by the specified tensor and omega comparisons. -/
def descendedEvaluation (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (CoefQbarTensor D l hl Ω X).obj
      (K, (descendedDual D l hl Ω X F hF).obj (op K)) ⟶ descendedOmega D l hl Ω X F :=
  (descendedTensorComparison D l hl Ω X F hF K.stage K.obj).inv ≫
    (inclusion K.stage).map ((F.datum K.stage).evaluation K.obj) ≫
      (descendedOmegaComparison D l hl Ω X F K.stage).hom

/-- The normalization of evaluation at an included finite object is definitional
up to cancellation of the specified tensor comparison. -/
theorem descendedEvaluation_finite (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) (K : Stage l Ω X E) :
    (tensorInclusion D l hl Ω X E K ((F.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion E).obj K))
          ((descendedComparison D l hl Ω X F hF E).hom.app (op K))) ≫
      descendedEvaluation D l hl Ω X F hF ((inclusion E).obj K) =
    (inclusion E).map ((F.datum E).evaluation K) ≫
      (descendedOmegaComparison D l hl Ω X F E).hom := by
  rw [← Category.assoc]
  change (descendedTensorComparison D l hl Ω X F hF E K).hom ≫
    ((descendedTensorComparison D l hl Ω X F hF E K).inv ≫ _) = _
  erw [Iso.hom_inv_id_assoc]
  rfl

attribute [local irreducible] tensorInclusion descendedDual descendedComparison
  descendedTensorComparison descendedEvaluation descendedOmegaComparison

private theorem q3_whisker_eqToIso
    {C : Type*} [Category C] {B : Type*} [Category B] {A : Type*} [Category A]
    {F G : C ⥤ B} (h : F = G) (J : B ⥤ A) :
    eqToIso (congrArg (fun H : C ⥤ B ↦ H ⋙ J) h) =
      Functor.isoWhiskerRight (eqToIso h) J := by
  subst G
  apply Iso.ext
  ext K
  simp

private theorem q3_inclusionTransition_eq (E L : Index l Ω) (h : E ≤ L) :
    inclusionTransition l Ω X E L h =
      Functor.isoWhiskerRight (operationStageTransitionIso l Ω X E L h).symm
        (inclusion L) ≪≫ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h := by
  unfold inclusionTransition operationStageTransitionIso
  rw [q3_whisker_eqToIso
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
      E L h).symm]
  rfl

private theorem q3_inclusionTransition_hom (E L : Index l Ω) (h : E ≤ L)
    (K : Stage l Ω X E) :
    (inclusionTransition l Ω X E L h).hom.app K =
      (inclusion L).map ((operationStageTransitionIso l Ω X E L h).inv.app K) ≫
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app K := by
  rw [q3_inclusionTransition_eq]
  rfl

private theorem q3_descendedOmegaComparison_stage (F : Finite D l hl Ω X) (E : Index l Ω) :
    descendedOmegaComparison D l hl Ω X F E =
      (inclusion E).mapIso
          (finiteOmegaStageComparison D l hl Ω X F
            (show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le)).symm ≪≫
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso
          (show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le)).app
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)) X).obj
              (F.omega (Padic.finiteCoefficientBase l Ω)).omega) := by
  unfold descendedOmegaComparison
  dsimp only
  erw [q3_inclusionTransition_eq]
  apply Iso.ext
  let O := Padic.finiteCoefficientBase l Ω
  let h : O ≤ E := show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le
  let W := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω O) X).obj
    (F.omega O).omega
  let q := (operationStageTransitionIso l Ω X O E h).app W
  let a := (F.scalar O E h).omega
  let t := ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).app W
  change (inclusion E).map a.inv ≫ ((inclusion E).map q.inv ≫ t.hom) =
    (inclusion E).map (a.inv ≫ q.inv) ≫ t.hom
  exact ((inclusion E).map_comp_assoc a.inv q.inv t.hom).symm

private theorem q3_descendedOmega_stage_square (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    (inclusion L).map (finiteOmegaStageComparison D l hl Ω X F h).hom ≫
        (descendedOmegaComparison D l hl Ω X F L).hom =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (F.omega E).omega) ≫ (descendedOmegaComparison D l hl Ω X F E).hom := by
  rw [q3_descendedOmegaComparison_stage, q3_descendedOmegaComparison_stage]
  exact q3_omega_from_base (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
    (fun E ↦ (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega)
    (fun {_ _} h ↦ finiteOmegaStageComparison D l hl Ω X F h)
    (fun {_ _ _} h k ↦ finiteOmegaStageComparison_tower D l hl Ω X F h k)
    (Padic.finiteCoefficientBase l Ω)
    (fun E ↦ show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le) h

private theorem q3_descendedOmega_square (F : Finite D l hl Ω X)
    (E L : Index l Ω) (h : E ≤ L) :
    (inclusion L).map (F.scalar E L h).omega.hom ≫
        (descendedOmegaComparison D l hl Ω X F L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (F.omega E).omega) ≫ (descendedOmegaComparison D l hl Ω X F E).hom := by
  let q := (inclusion L).mapIso ((operationStageTransitionIso l Ω X E L h).app
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega))
  apply (cancel_epi q.hom).mp
  dsimp only [q, Functor.mapIso_hom, Iso.app]
  have ht := q3_descendedOmega_stage_square D l hl Ω X F h
  rw [q3_inclusionTransition_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((inclusion L).map_comp_assoc
    ((operationStageTransitionIso l Ω X E L h).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (F.omega E).omega))
    (F.scalar E L h).omega.hom
    (descendedOmegaComparison D l hl Ω X F L).hom).symm.trans ht

private theorem q3_descendedEvaluation_inclusion (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω)
    {K M : Stage l Ω X E} (f : K ⟶ M) :
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom ((inclusion E).map f) (𝟙 _)) ≫
        descendedEvaluation D l hl Ω X F hF ((inclusion E).obj M) =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 _) ((descendedDual D l hl Ω X F hF).map
          ((inclusion E).map f).op)) ≫
        descendedEvaluation D l hl Ω X F hF ((inclusion E).obj K) := by
  exact q3_included_evaluation_natural
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E))
    (CoefQbarTensor D l hl Ω X) (inclusion E) (F.datum E).dual
    (descendedDual D l hl Ω X F hF)
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj (F.omega E).omega)
    (descendedOmega D l hl Ω X F) (F.datum E).evaluation
    (descendedEvaluation D l hl Ω X F hF) (descendedComparison D l hl Ω X F hF E)
    (descendedOmegaComparison D l hl Ω X F E) (tensorInclusion D l hl Ω X E)
    (fun {_ _} f ↦ (F.datum E).evaluation_natural _ _ f)
    (fun {_ _ _ _} f g ↦ (tensorInclusion_coherent D l hl Ω X).1 E f g)
    (descendedEvaluation_finite D l hl Ω X F hF E) f

private def q3_finiteDualStageComparison (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    (F.datum E).dual ⋙ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).op ⋙
        (F.datum L).dual :=
  Functor.isoWhiskerLeft (F.datum E).dual (operationStageTransitionIso l Ω X E L h) ≪≫
    F.beta E L h ≪≫
      Functor.isoWhiskerRight (NatIso.op (operationStageTransitionIso l Ω X E L h))
        (F.datum L).dual

private theorem q3_finiteDualStageComparison_hom (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) (K : Stage l Ω X E) :
    (q3_finiteDualStageComparison D l hl Ω X F h).hom.app (op K) =
      (operationStageTransitionIso l Ω X E L h).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.beta E L h).hom.app (op K) ≫
          (F.datum L).dual.map ((operationStageTransitionIso l Ω X E L h).hom.app K).op := by
  rfl

private theorem q3_descendedComparison_transition (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) {E L : Index l Ω} (h : E ≤ L)
    (K : Stage l Ω X E) :
    (inclusion L).map ((q3_finiteDualStageComparison D l hl Ω X F h).hom.app (op K)) ≫
        (descendedComparison D l hl Ω X F hF L).hom.app
          (op (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K)) ≫
        (descendedDual D l hl Ω X F hF).map
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).inv.app
            K).op =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app
          ((F.datum E).dual.obj (op K)) ≫
        (descendedComparison D l hl Ω X F hF E).hom.app (op K) := by
  rw [q3_finiteDualStageComparison_hom]
  unfold descendedComparison descendedDual finiteMorphism
  exact q3_transported_contravariant_transition
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) (literalSystem l Ω X)
    (stageSystem_eq_literalSystem l Ω X) (fun E ↦ (F.datum E).dual)
    (fun {_ _} h ↦ F.beta _ _ h)
    (fun {_ _ _} h k K ↦ eq_of_heq (hF.2 _ _ _ h k K)) h K

private theorem q3_descendedEvaluation_transition (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) {E L : Index l Ω} (h : E ≤ L)
    (K : Stage l Ω X E) :
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app K)
          (𝟙 _)) ≫ descendedEvaluation D l hl Ω X F hF ((inclusion E).obj K) =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 _) ((descendedDual D l hl Ω X F hF).map
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app
            K).op)) ≫ descendedEvaluation D l hl Ω X F hF
              ((inclusion L).obj
                (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K)) := by
  let := RationalVerdier.units D l hl X
  apply q3_evaluation_transition_paste
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E))
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L))
    (CoefQbarTensor D l hl Ω X)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
    (inclusion E) (inclusion L) (F.datum E).dual (F.datum L).dual
    (descendedDual D l hl Ω X F hF)
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj (F.omega E).omega)
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj (F.omega L).omega)
    (descendedOmega D l hl Ω X F) (F.datum E).evaluation (F.datum L).evaluation
    (descendedEvaluation D l hl Ω X F hF)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h)
    (q3_finiteDualStageComparison D l hl Ω X F h)
    (finiteOmegaStageComparison D l hl Ω X F h)
    (descendedComparison D l hl Ω X F hF E) (descendedComparison D l hl Ω X F hF L)
    (descendedOmegaComparison D l hl Ω X F E) (descendedOmegaComparison D l hl Ω X F L)
    (rationalTensorStageComparison l Ω X h)
    (tensorInclusion D l hl Ω X E) (tensorInclusion D l hl Ω X L)
    (fun {_ _ _ _} f g ↦ (tensorInclusion_coherent D l hl Ω X).1 L f g)
    (fun K P ↦ (tensorInclusion_coherent D l hl Ω X).2 h K P)
    (fun K ↦ q3_descendedComparison_transition D l hl Ω X F hF h K)
    (q3_descendedOmega_stage_square D l hl Ω X F h)
    (fun K ↦ ?_)
    (descendedEvaluation_finite D l hl Ω X F hF E)
    (descendedEvaluation_finite D l hl Ω X F hF L) K
  change (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L)).map
      (Prod.mkHom
        (𝟙 (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K))
        ((operationStageTransitionIso l Ω X E L h).hom.app ((F.datum E).dual.obj (op K)) ≫
          (F.beta E L h).hom.app (op K) ≫
            (F.datum L).dual.map ((operationStageTransitionIso l Ω X E L h).hom.app K).op)) ≫
      (F.datum L).evaluation
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).obj K) =
    (rationalTensorStageComparison l Ω X h).inv.app (K, (F.datum E).dual.obj (op K)) ≫
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).map
        ((F.datum E).evaluation K) ≫
      (operationStageTransitionIso l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (F.omega E).omega) ≫ (F.scalar E L h).omega.hom
  exact finite_evaluation_scalar_of_stages D l hl Ω X F h K

/-- The constructed omega comparisons are coherent and evaluation is natural.
Source: thm-coef-qbar-verdier, proof steps 4--5, common-stage evaluation descent
(blueprint: lem-coef-qbar-verdier-evaluation-equations).

Proof: for base <= E <= L, the three finite scalar u maps compose through the
prescribed tensor associator. This follows by localizing the canonical integral
u tower equation: the normalized reduction maps agree at every finite quotient,
so derived completeness identifies the two maps. Naturality and the cocycle of
the inclusion-transition isomorphisms then give the displayed omega equation.
For an arrow K -> M, choose a common stage representing it. Expand the two
constructed evaluations there using the finite scalar evaluation square and the
omega equation just proved. The representative formula for descendedDual
conjugates the finite dual arrow by beta and inverse beta. The two tensor
comparison factors therefore cancel against the finite scalar evaluation
square. What remains is precisely (F.datum L).evaluation_natural at that common
stage L. Include this equality; compatibility with further extension proves it
for the quotient class. Equal fields, zero objects, and zero arrows use the
same equations, so no nonzero or positive-dimensional hypothesis is needed. -/
theorem descendedEvaluation_equations (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    (∀ (E L : Index l Ω) (h : E ≤ L),
      (inclusion (Y := X) L).map (F.scalar E L h).omega.hom ≫
        (descendedOmegaComparison D l hl Ω X F L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (F.omega E).omega) ≫ (descendedOmegaComparison D l hl Ω X F E).hom) ∧
    (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X) (f : K ⟶ M),
      (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom f (𝟙 ((descendedDual D l hl Ω X F hF).obj (op M)))) ≫
        descendedEvaluation D l hl Ω X F hF M =
      (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom (𝟙 K) ((descendedDual D l hl Ω X F hF).map f.op)) ≫
        descendedEvaluation D l hl Ω X F hF K) := by
  refine ⟨q3_descendedOmega_square D l hl Ω X F, ?_⟩
  intro K M f
  induction f using CategoryTheory.StageSystem.PairCategory.hom_induction with
  | h L hK hM f =>
    rw [CategoryTheory.StageSystem.mkHom_eq_isoToStage]
    apply q3_dinatural_comp (CoefQbarTensor D l hl Ω X)
      (descendedDual D l hl Ω X F hF) (descendedOmega D l hl Ω X F)
      (descendedEvaluation D l hl Ω X F hF)
    · exact q3_dinatural_inv (CoefQbarTensor D l hl Ω X)
        (descendedDual D l hl Ω X F hF) (descendedOmega D l hl Ω X F)
        (descendedEvaluation D l hl Ω X F hF)
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso hK).app K.obj)
        (q3_descendedEvaluation_transition D l hl Ω X F hF hK K.obj)
    · exact q3_dinatural_comp (CoefQbarTensor D l hl Ω X)
        (descendedDual D l hl Ω X F hF) (descendedOmega D l hl Ω X F)
        (descendedEvaluation D l hl Ω X F hF) ((inclusion L).map f)
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage M hM).inv)
        (q3_descendedEvaluation_inclusion D l hl Ω X F hF L f)
        (q3_descendedEvaluation_transition D l hl Ω X F hF hM M.obj)

end WeilConjectures.CoefQbarVerdier
