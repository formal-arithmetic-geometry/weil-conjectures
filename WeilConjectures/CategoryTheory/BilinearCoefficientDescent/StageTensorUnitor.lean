/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
public import WeilConjectures.CategoryTheory.StageSystem.IsoOfTransport
public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.StageTensorBraiding

/-! # Unitor representatives in a directed tensor family

Natural left and right unitors at the finite stages, together with scalar unit comparisons
satisfying the two unit squares, descend to isomorphisms of the common-stage tensor objects
with the prescribed representative at every common stage. Uniqueness of the scalar unit
comparisons gives their cocycle law.
The derived-tensor application follows Stacks 06YS, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.BilinearCoefficientDescent.output

namespace CategoryTheory.BilinearCoefficientDescent

variable {I : Type w} [Preorder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)

variable (R : ∀ i, C i)
  (lam : ∀ i (X : C i), (U.U i).obj (R i, X) ≅ X)
  (rho : ∀ i (X : C i), (U.U i).obj (X, R i) ≅ X)

/-- The left unit square is stable under composing scalar unit comparisons. -/
theorem leftUnitSquare_trans
    (lamNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom (𝟙 (R i)) f) ≫ (lam i X').hom = (lam i X).hom ≫ f)
    {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (a : (S.T h).obj (R i) ≅ R j) (b : (S.T h').obj (R j) ≅ R k)
    (ha : ∀ X : C i, (U.comparison h).hom.app (R i, X) ≫
      (U.U j).map (Prod.mkHom a.hom (𝟙 _)) ≫ (lam j ((S.T h).obj X)).hom =
        (S.T h).map (lam i X).hom)
    (hb : ∀ X : C j, (U.comparison h').hom.app (R j, X) ≫
      (U.U k).map (Prod.mkHom b.hom (𝟙 _)) ≫ (lam k ((S.T h').obj X)).hom =
        (S.T h').map (lam j X).hom)
    (X : C i) :
    (U.comparison (h.trans h')).hom.app (R i, X) ≫
      (U.U k).map (Prod.mkHom
        ((S.assoc h h').inv.app (R i) ≫ (S.T h').map a.hom ≫ b.hom) (𝟙 _)) ≫
      (lam k ((S.T (h.trans h')).obj X)).hom =
        (S.T (h.trans h')).map (lam i X).hom := by
  have ht := U.tower h h' (R i) X
  rw [← cancel_epi ((S.assoc h h').hom.app ((U.U i).obj (R i, X)))]
  rw [← reassoc_of% ht]
  have hn := (S.assoc h h').hom.naturality (lam i X).hom
  simp only [Functor.comp_map] at hn
  rw [← hn, ← ha X]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← hb ((S.T h).obj X)]
  have hc := (U.comparison h').hom.naturality (Prod.mkHom a.hom (𝟙 ((S.T h).obj X)))
  simp only [Functor.comp_map, Functor.prod_map] at hc
  simp only [Category.assoc]
  rw [reassoc_of% hc, ← lamNat k ((S.T h').obj ((S.T h).obj X)) _ ((S.assoc h h').hom.app X)]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  ext
  · simp
  · simp

/-- The right unit square is stable under composing scalar unit comparisons. -/
theorem rightUnitSquare_trans
    (rhoNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom f (𝟙 (R i))) ≫ (rho i X').hom = (rho i X).hom ≫ f)
    {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (a : (S.T h).obj (R i) ≅ R j) (b : (S.T h').obj (R j) ≅ R k)
    (ha : ∀ X : C i, (U.comparison h).hom.app (X, R i) ≫
      (U.U j).map (Prod.mkHom (𝟙 _) a.hom) ≫ (rho j ((S.T h).obj X)).hom =
        (S.T h).map (rho i X).hom)
    (hb : ∀ X : C j, (U.comparison h').hom.app (X, R j) ≫
      (U.U k).map (Prod.mkHom (𝟙 _) b.hom) ≫ (rho k ((S.T h').obj X)).hom =
        (S.T h').map (rho j X).hom)
    (X : C i) :
    (U.comparison (h.trans h')).hom.app (X, R i) ≫
      (U.U k).map (Prod.mkHom (𝟙 _)
        ((S.assoc h h').inv.app (R i) ≫ (S.T h').map a.hom ≫ b.hom)) ≫
      (rho k ((S.T (h.trans h')).obj X)).hom =
        (S.T (h.trans h')).map (rho i X).hom := by
  have ht := U.tower h h' X (R i)
  rw [← cancel_epi ((S.assoc h h').hom.app ((U.U i).obj (X, R i)))]
  rw [← reassoc_of% ht]
  have hn := (S.assoc h h').hom.naturality (rho i X).hom
  simp only [Functor.comp_map] at hn
  rw [← hn, ← ha X]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← hb ((S.T h).obj X)]
  have hc := (U.comparison h').hom.naturality (Prod.mkHom (𝟙 ((S.T h).obj X)) a.hom)
  simp only [Functor.comp_map, Functor.prod_map] at hc
  simp only [Category.assoc]
  rw [reassoc_of% hc, ← rhoNat k ((S.T h').obj ((S.T h).obj X)) _ ((S.assoc h h').hom.app X)]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  ext
  · simp
  · simp

/-- Uniquely determined scalar unit comparisons satisfy the cocycle law. -/
theorem unitComparison_cocycle
    (lamNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom (𝟙 (R i)) f) ≫ (lam i X').hom = (lam i X).hom ≫ f)
    (rhoNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom f (𝟙 (R i))) ≫ (rho i X').hom = (rho i X).hom ≫ f)
    (s : ∀ {i j : I} (h : i ≤ j), (S.T h).obj (R i) ≅ R j)
    (hl : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (R i, X) ≫
      (U.U j).map (Prod.mkHom (s h).hom (𝟙 _)) ≫ (lam j ((S.T h).obj X)).hom =
        (S.T h).map (lam i X).hom)
    (hr : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (X, R i) ≫
      (U.U j).map (Prod.mkHom (𝟙 _) (s h).hom) ≫ (rho j ((S.T h).obj X)).hom =
        (S.T h).map (rho i X).hom)
    (huniq : ∀ {i j : I} (h : i ≤ j) (e : (S.T h).obj (R i) ≅ R j),
      (∀ X : C i, (U.comparison h).hom.app (R i, X) ≫
        (U.U j).map (Prod.mkHom e.hom (𝟙 _)) ≫ (lam j ((S.T h).obj X)).hom =
          (S.T h).map (lam i X).hom) →
      (∀ X : C i, (U.comparison h).hom.app (X, R i) ≫
        (U.U j).map (Prod.mkHom (𝟙 _) e.hom) ≫ (rho j ((S.T h).obj X)).hom =
          (S.T h).map (rho i X).hom) → e = s h)
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) :
    (S.assoc h h').inv.app (R i) ≫ (S.T h').map (s h).hom ≫ (s h').hom =
      (s (h.trans h')).hom := by
  have hc := huniq (h.trans h')
    (((S.assoc h h').app (R i)).symm ≪≫ (S.T h').mapIso (s h) ≪≫ s h')
    (leftUnitSquare_trans S U R lam lamNat h h' (s h) (s h') (hl h) (hl h'))
    (rightUnitSquare_trans S U R rho rhoNat h h' (s h) (s h') (hr h) (hr h'))
  exact congrArg Iso.hom hc

variable (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
  (s : ∀ {i j : I} (h : i ≤ j), (S.T h).obj (R i) ≅ R j)

/-- The stage representative of the common-stage left unitor. -/
def leftUnitorAt (b : I) (M : S.PairCategory) (L : I) (h : join b M.stage ≤ L) :
    (S.T h).obj (output U join left right (⟨b, R b⟩, M)).obj ≅
      M.toStage ((right _ _).trans h) :=
  endpoint U join left right (⟨b, R b⟩, M) h ≪≫
    (U.U L).mapIso (Iso.prod (s ((left _ _).trans h)) (Iso.refl _)) ≪≫
    lam L (M.toStage ((right _ _).trans h))

/-- The stage representative of the common-stage right unitor. -/
def rightUnitorAt (b : I) (M : S.PairCategory) (L : I) (h : join M.stage b ≤ L) :
    (S.T h).obj (output U join left right (M, ⟨b, R b⟩)).obj ≅
      M.toStage ((left _ _).trans h) :=
  endpoint U join left right (M, ⟨b, R b⟩) h ≪≫
    (U.U L).mapIso (Iso.prod (Iso.refl _) (s ((right _ _).trans h))) ≪≫
    rho L (M.toStage ((left _ _).trans h))

/-- The left unitor representatives are compatible with enlarging the stage. -/
theorem leftUnitorAt_transport
    (lamNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom (𝟙 (R i)) f) ≫ (lam i X').hom = (lam i X).hom ≫ f)
    (hl : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (R i, X) ≫
      (U.U j).map (Prod.mkHom (s h).hom (𝟙 _)) ≫ (lam j ((S.T h).obj X)).hom =
        (S.T h).map (lam i X).hom)
    (hcoc : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.assoc h h').inv.app (R i) ≫ (S.T h').map (s h).hom ≫ (s h').hom =
        (s (h.trans h')).hom)
    (b : I) (M : S.PairCategory) {L H : I} (h : join b M.stage ≤ L) (k : L ≤ H) :
    S.tr k (leftUnitorAt S U R lam join left right s b M L h).hom =
      (leftUnitorAt S U R lam join left right s b M H (h.trans k)).hom := by
  unfold StageSystem.tr
  rw [← cancel_epi ((S.assoc h k).hom.app (output U join left right (⟨b, R b⟩, M)).obj)]
  dsimp only [leftUnitorAt, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc, Iso.prod_hom,
    Iso.refl_hom]
  rw [reassoc_of% (endpoint_tower S U join left right ⟨b, R b⟩ M h k)]
  congr 1
  rw [← hl k (M.toStage ((right _ _).trans h))]
  have hc := (U.comparison k).hom.naturality
    (Prod.mkHom (s ((left b M.stage).trans h)).hom (𝟙 (M.toStage ((right _ _).trans h))))
  simp only [Functor.comp_map, Functor.prod_map] at hc
  simp only [Category.assoc]
  rw [reassoc_of% hc, ← lamNat H ((S.T k).obj (M.toStage ((right _ _).trans h))) _
    ((S.assoc ((right _ _).trans h) k).hom.app M.obj)]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  ext
  · have hk := hcoc ((left b M.stage).trans h) k
    rw [← cancel_epi ((S.assoc ((left b M.stage).trans h) k).inv.app (R b))]
    simp only [prod_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
    simpa using hk
  · simp

/-- The right unitor representatives are compatible with enlarging the stage. -/
theorem rightUnitorAt_transport
    (rhoNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom f (𝟙 (R i))) ≫ (rho i X').hom = (rho i X).hom ≫ f)
    (hr : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (X, R i) ≫
      (U.U j).map (Prod.mkHom (𝟙 _) (s h).hom) ≫ (rho j ((S.T h).obj X)).hom =
        (S.T h).map (rho i X).hom)
    (hcoc : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.assoc h h').inv.app (R i) ≫ (S.T h').map (s h).hom ≫ (s h').hom =
        (s (h.trans h')).hom)
    (b : I) (M : S.PairCategory) {L H : I} (h : join M.stage b ≤ L) (k : L ≤ H) :
    S.tr k (rightUnitorAt S U R rho join left right s b M L h).hom =
      (rightUnitorAt S U R rho join left right s b M H (h.trans k)).hom := by
  unfold StageSystem.tr
  rw [← cancel_epi ((S.assoc h k).hom.app (output U join left right (M, ⟨b, R b⟩)).obj)]
  dsimp only [rightUnitorAt, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc, Iso.prod_hom,
    Iso.refl_hom]
  rw [reassoc_of% (endpoint_tower S U join left right M ⟨b, R b⟩ h k)]
  congr 1
  rw [← hr k (M.toStage ((left _ _).trans h))]
  have hc := (U.comparison k).hom.naturality
    (Prod.mkHom (𝟙 (M.toStage ((left _ _).trans h))) (s ((right M.stage b).trans h)).hom)
  simp only [Functor.comp_map, Functor.prod_map] at hc
  simp only [Category.assoc]
  rw [reassoc_of% hc, ← rhoNat H ((S.T k).obj (M.toStage ((left _ _).trans h))) _
    ((S.assoc ((left _ _).trans h) k).hom.app M.obj)]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  ext
  · simp
  · have hk := hcoc ((right M.stage b).trans h) k
    rw [← cancel_epi ((S.assoc ((right M.stage b).trans h) k).inv.app (R b))]
    simp only [prod_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
    simpa using hk

variable [IsDirectedOrder I]

/-- The left unitor representatives define an isomorphism of the pair category. Here `hl` is
the left unit square for `h : i ≤ j` (writing `⊗` for `U.U`, `T` for `S.T h`, `c` for the
comparison and `s` for the scalar unit comparison)
```
T(R_i ⊗ X) --c--> TR_i ⊗ TX --s ⊗ 1--> R_j ⊗ TX
     |                                   |
   T λ                                   λ
     v                                   v
    TX ================================ TX
```
and `hcoc` is the cocycle law of `s`. -/
theorem leftUnitor_exists
    (lamNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom (𝟙 (R i)) f) ≫ (lam i X').hom = (lam i X).hom ≫ f)
    (hl : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (R i, X) ≫
      (U.U j).map (Prod.mkHom (s h).hom (𝟙 _)) ≫ (lam j ((S.T h).obj X)).hom =
        (S.T h).map (lam i X).hom)
    (hcoc : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.assoc h h').inv.app (R i) ≫ (S.T h').map (s h).hom ≫ (s h').hom =
        (s (h.trans h')).hom)
    (b : I) (M : S.PairCategory) :
    ∃ e : output U join left right (⟨b, R b⟩, M) ≅ M,
      ∀ (L : I) (h : join b M.stage ≤ L) (hM : M.stage ≤ L),
        e.hom = StageSystem.PairCategory.mkHom L h hM
          (leftUnitorAt S U R lam join left right s b M L h).hom :=
  StageSystem.PairCategory.exists_iso_of_tr (S := S) (X := output U join left right (⟨b, R b⟩, M))
    (Y := M) (fun L h _ ↦ leftUnitorAt S U R lam join left right s b M L h)
    (fun _ _ h _ k ↦ leftUnitorAt_transport S U R lam join left right s lamNat hl hcoc b M h k)

/-- The right unitor representatives define an isomorphism of the pair category. Here `hr` is
the right unit square for `h : i ≤ j` (notation as in `leftUnitor_exists`)
```
T(X ⊗ R_i) --c--> TX ⊗ TR_i --1 ⊗ s--> TX ⊗ R_j
     |                                   |
   T ρ                                   ρ
     v                                   v
    TX ================================ TX
```
and `hcoc` is the cocycle law of `s`. -/
theorem rightUnitor_exists
    (rhoNat : ∀ i (X X' : C i) (f : X ⟶ X'),
      (U.U i).map (Prod.mkHom f (𝟙 (R i))) ≫ (rho i X').hom = (rho i X).hom ≫ f)
    (hr : ∀ {i j : I} (h : i ≤ j) (X : C i), (U.comparison h).hom.app (X, R i) ≫
      (U.U j).map (Prod.mkHom (𝟙 _) (s h).hom) ≫ (rho j ((S.T h).obj X)).hom =
        (S.T h).map (rho i X).hom)
    (hcoc : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      (S.assoc h h').inv.app (R i) ≫ (S.T h').map (s h).hom ≫ (s h').hom =
        (s (h.trans h')).hom)
    (b : I) (M : S.PairCategory) :
    ∃ e : output U join left right (M, ⟨b, R b⟩) ≅ M,
      ∀ (L : I) (h : join M.stage b ≤ L) (hM : M.stage ≤ L),
        e.hom = StageSystem.PairCategory.mkHom L h hM
          (rightUnitorAt S U R rho join left right s b M L h).hom :=
  StageSystem.PairCategory.exists_iso_of_tr (S := S) (X := output U join left right (M, ⟨b, R b⟩))
    (Y := M) (fun L h _ ↦ rightUnitorAt S U R rho join left right s b M L h)
    (fun _ _ h _ k ↦ rightUnitorAt_transport S U R rho join left right s rhoNat hr hcoc b M h k)

end CategoryTheory.BilinearCoefficientDescent
