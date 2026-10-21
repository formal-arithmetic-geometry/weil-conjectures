/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.PbcCommonStageCones
import Sheaf.Paper.PbcVerdierAxioms

/-! # Simultaneous lifting of distinguished rows and finite equations

Source: blueprint `main-20261015`, `thm-weil-pbc-verdier-axioms.proof.md`, TR2--TR4
common-stage representation sentences (blueprint: lem-weil-pbc-distinguished-diagram-lifting).

The expression helpers encode only finite terms, with typed endpoints. An occurrence
is an original vertex together with a number of applications of [1]. Raw stage objects
are scalar extensions of these occurrences; their shift comparison is the prescribed sigma.
No triangulation of the pair category is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b e r w u v c

open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.PbcFiniteDiagram

/-- An occurrence of a vertex after finitely many shifts [1]. Source: blueprint TR2--TR4
finite data (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Vertex (A : Type a) where
  index : A
  shifts : ℕ

/-- One more occurrence of [1]. Source: blueprint TR2--TR4 finite data
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Vertex.shift {A : Type a} (x : Vertex A) : Vertex A := ⟨x.index, x.shifts + 1⟩

/-- Iterated [1], retaining parentheses and the zero-iteration identity literally.
Source: blueprint repeated shifts (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def iterShift {D : Type u} [Category.{v} D] [HasShift D ℤ] (K : D) : ℕ → D
  | 0 => K
  | n + 1 => (shiftFunctor D (1 : ℤ)).obj (iterShift K n)

/-- Typed terms in the specified arrows and the permitted operations. Each term is finite.
Source: blueprint TR2--TR4 finite equations
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
inductive Expr {A : Type a} {B : Type b} (s t : B → Vertex A) :
    Vertex A → Vertex A → Type (max a b)
  | arrow (k : B) : Expr s t (s k) (t k)
  | id (x : Vertex A) : Expr s t x x
  | zero (x y : Vertex A) : Expr s t x y
  | comp {x y z : Vertex A} : Expr s t x y → Expr s t y z → Expr s t x z
  | add {x y : Vertex A} : Expr s t x y → Expr s t x y → Expr s t x y
  | neg {x y : Vertex A} : Expr s t x y → Expr s t x y
  | shift {x y : Vertex A} : Expr s t x y → Expr s t x.shift y.shift

/-- Evaluation uses the stated shift identifications: sigma_X, then u[1], then
sigma_Y inverse. Source: blueprint common-stage shift formula
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Expr.eval {A : Type a} {B : Type b} {s t : B → Vertex A}
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    (V : Vertex A → D) (sigma : ∀ x : Vertex A, V x.shift ≅ (V x)⟦(1 : ℤ)⟧)
    (f : ∀ k : B, V (s k) ⟶ V (t k)) :
    {x y : Vertex A} → Expr s t x y → (V x ⟶ V y)
  | _, _, .arrow k => f k
  | _, _, .id x => 𝟙 (V x)
  | _, _, .zero _ _ => 0
  | _, _, .comp p q => p.eval V sigma f ≫ q.eval V sigma f
  | _, _, .add p q => p.eval V sigma f + q.eval V sigma f
  | _, _, .neg p => -p.eval V sigma f
  | _, _, @Expr.shift _ _ _ _ x y p =>
      (sigma x).hom ≫ (shiftFunctor D (1 : ℤ)).map (p.eval V sigma f) ≫ (sigma y).inv

/-- A selected equation consists of parallel finite terms. Source: blueprint finite
asserted equalities (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Equation {A : Type a} {B : Type b} (s t : B → Vertex A) where
  source : Vertex A
  target : Vertex A
  lhs : Expr s t source target
  rhs : Expr s t source target

/-- A selected row uses three occurrences and terms ending in the shifted first occurrence.
Source: blueprint distinguished rows
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
structure Row {A : Type a} {B : Type b} (s t : B → Vertex A) where
  first : Vertex A
  second : Vertex A
  third : Vertex A
  f : Expr s t first second
  i : Expr s t second third
  p : Expr s t third first.shift

/-- The triangle of a row, correcting its last arrow by sigma. Source: blueprint displayed
lifted row (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def Row.triangle {A : Type a} {B : Type b} {s t : B → Vertex A}
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    (V : Vertex A → D) (sigma : ∀ x : Vertex A, V x.shift ≅ (V x)⟦(1 : ℤ)⟧)
    (f : ∀ k : B, V (s k) ⟶ V (t k)) (R : Row s t) : Triangle D :=
  Triangle.mk (R.f.eval V sigma f) (R.i.eval V sigma f)
    (R.p.eval V sigma f ≫ (sigma R.first).hom)

end CategoryTheory.PbcFiniteDiagram

namespace CategoryTheory.StageSystem

open CategoryTheory.PbcFiniteDiagram

section DiagramLifting
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, Preadditive (C i)] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ i, HasShift (C i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]

private abbrev diagramVertex {A : Type a} (X : A → S.PairCategory) (x : Vertex A) :
    S.PairCategory := ⟨(X x.index).stage, iterShift (X x.index).obj x.shifts⟩

private abbrev diagramSigma {A : Type a} (X : A → S.PairCategory)
    {M : I} (h : ∀ j, (X j).stage ≤ M) (x : Vertex A) :
    (diagramVertex S X x.shift).toStage (h x.index) ≅
      ((diagramVertex S X x).toStage (h x.index))⟦(1 : ℤ)⟧ :=
  ((S.T (h x.index)).commShiftIso (1 : ℤ)).app
    (iterShift (X x.index).obj x.shifts)

private abbrev diagramPairSigma {A : Type a} (X : A → S.PairCategory) (x : Vertex A) :
    diagramVertex S X x.shift ≅ (diagramVertex S X x)⟦(1 : ℤ)⟧ := Iso.refl _

private theorem diagramEq_refine {X Y : S.PairCategory} {M : I}
    {hX : X.stage ≤ M} {hY : Y.stage ≤ M}
    (u v : X.toStage hX ⟶ Y.toStage hY)
    (he : PairCategory.mkHom M hX hY u = PairCategory.mkHom M hX hY v) :
    ∃ (N : I) (h : M ≤ N), S.tr h u = S.tr h v := by
  obtain ⟨N, h, he⟩ := (PairCategory.mkHom_eq_mkHom_iff u v).mp he
  exact ⟨N, h, (tr_injective h).mpr he⟩

private theorem diagramIso_refine {X Y : S.PairCategory} {M : I}
    {hX : X.stage ≤ M} {hY : Y.stage ≤ M}
    (u : X.toStage hX ⟶ Y.toStage hY)
    (he : IsIso (PairCategory.mkHom M hX hY u)) :
    ∃ (N : I) (h : M ≤ N), IsIso (S.tr h u) := by
  let f := PairCategory.mkHom M hX hY u
  let _ : IsIso f := he
  obtain ⟨L, hL, hY', hX', v, hv⟩ := PairCategory.exists_le_mkHom_eq (inv f) M
  have hf : PairCategory.mkHom L (hX.trans hL) (hY.trans hL) (S.tr hL u) = f :=
    PairCategory.mkHom_tr hL u
  have h₁ : PairCategory.mkHom L (hX.trans hL) (hX.trans hL)
      (S.tr hL u ≫ v) =
      PairCategory.mkHom (X := X) (Y := X) L (hX.trans hL) (hX.trans hL) (𝟙 _) := by
    rw [← PairCategory.mkHom_comp_mkHom, hf, ← hv, ← PairCategory.id_eq_mkHom]
    exact IsIso.hom_inv_id f
  obtain ⟨P, hP, e₁⟩ := diagramEq_refine S _ _ h₁
  have h₂ : PairCategory.mkHom P (hY.trans (hL.trans hP))
      (hY.trans (hL.trans hP)) (S.tr hP v ≫ S.tr (hL.trans hP) u) =
      PairCategory.mkHom (X := Y) (Y := Y) P
        (hY.trans (hL.trans hP)) (hY.trans (hL.trans hP)) (𝟙 _) := by
    rw [← PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_tr,
      PairCategory.mkHom_tr, ← hv, ← PairCategory.id_eq_mkHom]
    exact IsIso.inv_hom_id f
  obtain ⟨N, hN, e₂⟩ := diagramEq_refine S _ _ h₂
  have hcomp₁ : S.tr (hL.trans (hP.trans hN)) u ≫ S.tr (hP.trans hN) v = 𝟙 _ := by
    have := congrArg (S.tr hN) e₁
    simpa only [tr_comp, tr_tr, tr_id] using this
  have hcomp₂ : S.tr (hP.trans hN) v ≫ S.tr (hL.trans (hP.trans hN)) u = 𝟙 _ := by
    simpa only [tr_comp, tr_tr, tr_id] using e₂
  exact ⟨N, hL.trans (hP.trans hN),
    ⟨⟨S.tr (hP.trans hN) v, hcomp₁, hcomp₂⟩⟩⟩

private theorem diagramNativeRepresentatives {D : Type a} [Finite D] {i : I}
    (X Y : D → C i) (f : ∀ d, (S.ι i).obj (X d) ⟶ (S.ι i).obj (Y d)) :
    ∃ (j : I) (h : i ≤ j) (u : ∀ d, (S.T h).obj (X d) ⟶ (S.T h).obj (Y d)),
      ∀ d, PairCategory.mkHom (X := (S.ι i).obj (X d))
        (Y := (S.ι i).obj (Y d)) j h h (u d) = f d := by
  classical
  choose k hX hY hk using fun d ↦ PairCategory.exists_mkHom_eq (f d)
  obtain ⟨j, hj⟩ := Finite.exists_le (fun d : Option D ↦ d.elim i k)
  choose u hu using fun d ↦ hk d j (hj (some d))
  exact ⟨j, hj none, u, fun d ↦ (hu d).symm⟩

private theorem diagramNativeIsIso {i : I} {X Y : C i} (f : X ⟶ Y)
    (hf : IsIso ((S.ι i).map f)) :
    ∃ (j : I) (h : i ≤ j), IsIso ((S.T h).map f) := by
  rw [ι_map_eq (le_refl i)] at hf
  obtain ⟨j, h, hj⟩ := diagramIso_refine S _ hf
  rw [tr_map] at hj
  exact ⟨j, h, hj⟩

private theorem diagramNativeEq_trans {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    {X Y : C i} {f g : X ⟶ Y} (he : (S.T h).map f = (S.T h).map g) :
    (S.T (h.trans h')).map f = (S.T (h.trans h')).map g := by
  have := congrArg (S.T h').map he
  simpa only [map_map_eq, ← Category.assoc, cancel_mono, cancel_epi] using this

private theorem diagramNativeEqualities {D : Type a} [Finite D] {i : I}
    (X Y : D → C i) (f g : ∀ d, X d ⟶ Y d)
    (he : ∀ d, (S.ι i).map (f d) = (S.ι i).map (g d)) :
    ∃ (j : I) (h : i ≤ j), ∀ d, (S.T h).map (f d) = (S.T h).map (g d) := by
  classical
  choose k hk he using fun d ↦ (ι_map_eq_ι_map_iff (f d) (g d)).mp (he d)
  obtain ⟨j, hj⟩ := Finite.exists_le (fun d : Option D ↦ d.elim i k)
  exact ⟨j, hj none, fun d ↦ diagramNativeEq_trans S (hk d) (hj (some d)) (he d)⟩

private theorem diagramNativeIsos {D : Type a} [Finite D] {i : I}
    (X Y : D → C i) (f : ∀ d, X d ⟶ Y d)
    (he : ∀ d, IsIso ((S.ι i).map (f d))) :
    ∃ (j : I) (h : i ≤ j), ∀ d, IsIso ((S.T h).map (f d)) := by
  classical
  choose k hk he using fun d ↦ diagramNativeIsIso S (f d) (he d)
  obtain ⟨j, hj⟩ := Finite.exists_le (fun d : Option D ↦ d.elim i k)
  refine ⟨j, hj none, fun d ↦ ?_⟩
  let _ := he d
  exact (NatIso.isIso_map_iff (S.assoc (hk d) (hj (some d))) (f d)).mp
    (inferInstanceAs (IsIso ((S.T (hj (some d))).map ((S.T (hk d)).map (f d)))))

private theorem diagramExpr_represents {A : Type a} {B : Type b}
    (X : A → S.PairCategory) (s t : B → Vertex A)
    (f : ∀ k, diagramVertex S X (s k) ⟶ diagramVertex S X (t k))
    {M : I} (h : ∀ j, (X j).stage ≤ M)
    (u : ∀ k, (diagramVertex S X (s k)).toStage (h (s k).index) ⟶
      (diagramVertex S X (t k)).toStage (h (t k).index))
    (hu : ∀ k, PairCategory.mkHom (X := diagramVertex S X (s k))
      (Y := diagramVertex S X (t k)) M (h (s k).index) (h (t k).index) (u k) = f k)
    {x y : Vertex A} (p : Expr s t x y) :
    PairCategory.mkHom (X := diagramVertex S X x) (Y := diagramVertex S X y)
      M (h x.index) (h y.index)
      (p.eval (fun x ↦ (diagramVertex S X x).toStage (h x.index))
        (diagramSigma S X h) u) =
      p.eval (diagramVertex S X) (diagramPairSigma S X) f := by
  induction p with
  | arrow k => exact hu k
  | id x => exact (PairCategory.id_eq_mkHom (diagramVertex S X x) (h x.index)).symm
  | zero x y => exact ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ 0 0).2
  | comp p q hp hq =>
    simpa only [Expr.eval, ← PairCategory.mkHom_comp_mkHom] using congrArg₂ (· ≫ ·) hp hq
  | add p q hp hq =>
    rw [Expr.eval, ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ _ _).1,
      hp, hq, Expr.eval]
  | neg p hp =>
    dsimp only [Expr.eval]
    have hn : ∀ {U V : S.PairCategory} (hU : U.stage ≤ M) (hV : V.stage ≤ M)
        (v : U.toStage hU ⟶ V.toStage hV),
        PairCategory.mkHom M hU hV (-v) = -PairCategory.mkHom M hU hV v := by
      intro U V hU hV v
      apply eq_neg_of_add_eq_zero_left
      rw [← ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ _ _).1,
        neg_add_cancel]
      exact ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ 0 0).2
    rw [hn, hp]
  | @shift x y p hp =>
    dsimp only [Expr.eval]
    simp only [diagramPairSigma, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    rw [← hp]
    erw [Category.comp_id]
    rfl

private theorem diagramExpr_transport {A : Type a} {B : Type b}
    (X : A → S.PairCategory) (s t : B → Vertex A)
    {M N : I} (h : ∀ j, (X j).stage ≤ M) (k : M ≤ N)
    (u : ∀ j, (diagramVertex S X (s j)).toStage (h (s j).index) ⟶
      (diagramVertex S X (t j)).toStage (h (t j).index))
    {x y : Vertex A} (p : Expr s t x y) :
    S.tr k (p.eval (fun x ↦ (diagramVertex S X x).toStage (h x.index))
      (diagramSigma S X h) u) =
    p.eval (fun x ↦ (diagramVertex S X x).toStage ((h x.index).trans k))
      (diagramSigma S X (fun j ↦ (h j).trans k)) (fun j ↦ S.tr k (u j)) := by
  induction p with
  | arrow j => rfl
  | id x => exact tr_id k _
  | zero x y => simp [Expr.eval, tr]
  | comp p q hp hq => simp only [Expr.eval, tr_comp, hp, hq]
  | add p q hp hq => simp only [Expr.eval, tr, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp] at hp hq ⊢; rw [hp, hq]
  | neg p hp => simp only [Expr.eval, tr, Functor.map_neg,
      Preadditive.comp_neg, Preadditive.neg_comp] at hp ⊢; rw [hp]
  | @shift x y p hp =>
    change S.tr k ((pbcStageShift S (1 : ℤ)).mapAt _) = _
    rw [Morphism.tr_mapAt, hp]
    rfl

private noncomputable def diagramRow_transportIso {A : Type a} {B : Type b}
    (X : A → S.PairCategory) (s t : B → Vertex A)
    {M N : I} (h : ∀ j, (X j).stage ≤ M) (k : M ≤ N)
    (u : ∀ j, (diagramVertex S X (s j)).toStage (h (s j).index) ⟶
      (diagramVertex S X (t j)).toStage (h (t j).index)) (R : Row s t) :
    R.triangle (fun x ↦ (diagramVertex S X x).toStage ((h x.index).trans k))
        (diagramSigma S X (fun j ↦ (h j).trans k)) (fun j ↦ S.tr k (u j)) ≅
      (S.T k).mapTriangle.obj
        (R.triangle (fun x ↦ (diagramVertex S X x).toStage (h x.index))
          (diagramSigma S X h) u) := by
  refine Triangle.isoMk _ _
    ((S.assoc (h R.first.index) k).app (diagramVertex S X R.first).obj).symm
    ((S.assoc (h R.second.index) k).app (diagramVertex S X R.second).obj).symm
    ((S.assoc (h R.third.index) k).app (diagramVertex S X R.third).obj).symm ?_ ?_ ?_
  · dsimp only [Row.triangle, Functor.mapTriangle, Triangle.mk]
    rw [← diagramExpr_transport S X s t h k u R.f]
    simp only [tr, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    erw [Category.comp_id]
  · dsimp only [Row.triangle, Functor.mapTriangle, Triangle.mk]
    rw [← diagramExpr_transport S X s t h k u R.i]
    simp only [tr, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    erw [Category.comp_id]
  · dsimp only [Row.triangle, Functor.mapTriangle, Triangle.mk]
    rw [← diagramExpr_transport S X s t h k u R.p]
    simp only [tr, Functor.map_comp, Category.assoc]
    have coh := pbcStageShift_coherence S (1 : ℤ) (h R.first.index) k
      (diagramVertex S X R.first).obj
    have eq := congrArg
      (fun z ↦ (S.assoc (h R.third.index) k).inv.app
        (diagramVertex S X R.third).obj ≫ (S.T k).map
        (R.p.eval (fun x ↦ (diagramVertex S X x).toStage (h x.index))
          (diagramSigma S X h) u) ≫ z ≫
            (shiftFunctor (C N) (1 : ℤ)).map
              ((S.assoc (h R.first.index) k).inv.app
                (diagramVertex S X R.first).obj)) coh
    have eq' := eq.symm
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at eq'
    erw [Functor.map_id, Category.comp_id] at eq'
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [diagramSigma, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
        Category.assoc, Vertex.shift, iterShift, Functor.comp_obj] using eq'

private theorem diagramTransIsoCommShift {i j : I} (h : i ≤ j) :
    NatTrans.CommShift (S.transIso h).hom ℤ := by
  constructor
  intro n
  ext K
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((S.ι j).map (((S.T h).commShiftIso n).hom.app K) ≫
    𝟙 _) ≫ (pbcPairShift S n).map ((S.transIso h).hom.app K) =
    (S.transIso h).hom.app ((shiftFunctor (C i) n).obj K) ≫ 𝟙 _
  simp only [Category.comp_id]
  simp only [transIso_hom_app, isoToStage, pbcPairShift]
  erw [Morphism.functor_map_mkHom, ι_map_eq (le_rfl : j ≤ j),
    PairCategory.mkHom_comp_mkHom]
  congr 1
  change (S.T (le_rfl : j ≤ j)).map (((S.T h).commShiftIso n).hom.app K) ≫
    (((S.T (le_rfl : j ≤ j)).commShiftIso n).hom.app ((S.T h).obj K) ≫
      (shiftFunctor (C j) n).map ((S.assoc h le_rfl).hom.app K) ≫
        ((S.T h).commShiftIso n).inv.app K) =
    (S.assoc h le_rfl).hom.app ((shiftFunctor (C i) n).obj K)
  have eq := congrArg (fun f ↦ f ≫ ((S.T h).commShiftIso n).inv.app K)
    (pbcStageShift_coherence S n h le_rfl K)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
    Category.comp_id] using eq

private theorem diagramInclusionShift (i : I) (n : ℤ) (K : C i) :
    ((S.ι i).commShiftIso n).hom.app K = 𝟙 _ := rfl

private noncomputable def diagramTriangleStageIso {i j : I} (h : i ≤ j)
    (τ : Triangle (C i)) :
    (S.ι i).mapTriangle.obj τ ≅ (S.ι j).mapTriangle.obj ((S.T h).mapTriangle.obj τ) := by
  let _ := diagramTransIsoCommShift S h
  exact (Functor.mapTriangleIso (S.transIso h)).symm.app τ ≪≫
    (Functor.mapTriangleCompIso (S.T h) (S.ι j)).app τ

private theorem diagramTriangleIso_lift {i : I} (τ ρ : Triangle (C i))
    (e : (S.ι i).mapTriangle.obj τ ≅ (S.ι i).mapTriangle.obj ρ) :
    ∃ (j : I) (h : i ≤ j),
      Nonempty ((S.T h).mapTriangle.obj τ ≅ (S.T h).mapTriangle.obj ρ) := by
  classical
  let X : Option Bool → C i := fun
    | none => τ.obj₁ | some false => τ.obj₂ | some true => τ.obj₃
  let Y : Option Bool → C i := fun
    | none => ρ.obj₁ | some false => ρ.obj₂ | some true => ρ.obj₃
  let f : ∀ k, (S.ι i).obj (X k) ⟶ (S.ι i).obj (Y k) :=
    fun | none => e.hom.hom₁ | some false => e.hom.hom₂ | some true => e.hom.hom₃
  obtain ⟨J, hJ, u, hu⟩ := diagramNativeRepresentatives S X Y f
  let τJ := (S.T hJ).mapTriangle.obj τ
  let ρJ := (S.T hJ).mapTriangle.obj ρ
  let eJ := (diagramTriangleStageIso S hJ τ).symm ≪≫ e ≪≫
    diagramTriangleStageIso S hJ ρ
  have hmaps (k : Option Bool) : (S.ι J).map (u k) =
      (S.isoToStage ((S.ι i).obj (X k)) hJ).inv ≫ f k ≫
        (S.isoToStage ((S.ι i).obj (Y k)) hJ).hom := by
    exact (ι_map_eq_isoToStage (X := (S.ι i).obj (X k))
      (Y := (S.ι i).obj (Y k)) hJ hJ (u k)).trans
      (congrArg (fun v ↦ (S.isoToStage ((S.ι i).obj (X k)) hJ).inv ≫ v ≫
        (S.isoToStage ((S.ι i).obj (Y k)) hJ).hom) (hu k))
  have h₁ : (S.ι J).map (u none) = eJ.hom.hom₁ := by
    simp only [diagramTriangleStageIso, Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom,
      Iso.symm_hom, Iso.app_inv, Iso.symm_inv, Iso.app_hom, triangleCategory_comp,
      TriangleMorphism.comp_hom₁, Functor.mapTriangleCompIso_inv_app_hom₁,
      Functor.mapTriangleIso_hom_app_hom₁, transIso_hom_app,
      Functor.mapTriangleIso_inv_app_hom₁, transIso_inv_app,
      Functor.mapTriangleCompIso_hom_app_hom₁, eJ]
    erw [Category.id_comp, Category.comp_id]
    simpa [X, Y, f, ι_obj] using hmaps none
  have h₂ : (S.ι J).map (u (some false)) = eJ.hom.hom₂ := by
    simp only [diagramTriangleStageIso, Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom,
      Iso.symm_hom, Iso.app_inv, Iso.symm_inv, Iso.app_hom, triangleCategory_comp,
      TriangleMorphism.comp_hom₂, Functor.mapTriangleCompIso_inv_app_hom₂,
      Functor.mapTriangleIso_hom_app_hom₂, transIso_hom_app,
      Functor.mapTriangleIso_inv_app_hom₂, transIso_inv_app,
      Functor.mapTriangleCompIso_hom_app_hom₂, eJ]
    erw [Category.id_comp, Category.comp_id]
    simpa [X, Y, f, ι_obj] using hmaps (some false)
  have h₃ : (S.ι J).map (u (some true)) = eJ.hom.hom₃ := by
    simp only [diagramTriangleStageIso, Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom,
      Iso.symm_hom, Iso.app_inv, Iso.symm_inv, Iso.app_hom, triangleCategory_comp,
      TriangleMorphism.comp_hom₃, Functor.mapTriangleCompIso_inv_app_hom₃,
      Functor.mapTriangleIso_hom_app_hom₃, transIso_hom_app,
      Functor.mapTriangleIso_inv_app_hom₃, transIso_inv_app,
      Functor.mapTriangleCompIso_hom_app_hom₃, eJ]
    erw [Category.id_comp, Category.comp_id]
    simpa [X, Y, f, ι_obj] using hmaps (some true)
  have hiso (k : Option Bool) : IsIso ((S.ι J).map (u k)) := by
    rcases k with _ | (_ | _)
    · rw [h₁]; infer_instance
    · rw [h₂]; infer_instance
    · rw [h₃]; infer_instance
  obtain ⟨P, hP, hPiso⟩ := diagramNativeIsos S
    (fun k ↦ (S.T hJ).obj (X k)) (fun k ↦ (S.T hJ).obj (Y k)) u hiso
  let U : Option Bool → C J := fun
    | none => τJ.obj₁ | some false => τJ.obj₂ | some true => τJ.obj₃
  let V : Option Bool → C J := fun
    | none => ρJ.obj₂ | some false => ρJ.obj₃ | some true => ρJ.obj₁⟦(1 : ℤ)⟧
  let lhs : ∀ k, U k ⟶ V k := fun
    | none => τJ.mor₁ ≫ u (some false)
    | some false => τJ.mor₂ ≫ u (some true)
    | some true => τJ.mor₃ ≫ (shiftFunctor (C J) (1 : ℤ)).map (u none)
  let rhs : ∀ k, U k ⟶ V k := fun
    | none => u none ≫ ρJ.mor₁
    | some false => u (some false) ≫ ρJ.mor₂
    | some true => u (some true) ≫ ρJ.mor₃
  have heq (k : Option Bool) : (S.ι J).map (lhs k) = (S.ι J).map (rhs k) := by
    rcases k with _ | (_ | _)
    · simpa [lhs, rhs, U, V, τJ, ρJ, Functor.mapTriangle, Triangle.mk, h₁, h₂] using eJ.hom.comm₁
    · simpa [lhs, rhs, U, V, τJ, ρJ, Functor.mapTriangle, Triangle.mk, h₂, h₃] using eJ.hom.comm₂
    · have nat := ((S.ι J).commShiftIso (1 : ℤ)).hom.naturality (u none)
      have comm := eJ.hom.comm₃
      change ((S.ι J).map τJ.mor₃ ≫ 𝟙 _) ≫
        (shiftFunctor S.PairCategory (1 : ℤ)).map eJ.hom.hom₁ =
          eJ.hom.hom₃ ≫ ((S.ι J).map ρJ.mor₃ ≫ 𝟙 _) at comm
      change (S.ι J).map ((shiftFunctor (C J) (1 : ℤ)).map (u none)) ≫ 𝟙 _ =
        𝟙 _ ≫ (shiftFunctor S.PairCategory (1 : ℤ)).map ((S.ι J).map (u none)) at nat
      simp only [Category.comp_id, Category.id_comp] at nat comm
      rw [← h₁, ← h₃, ← nat] at comm
      simpa [lhs, rhs] using comm
  obtain ⟨L, hL, hLeq⟩ := diagramNativeEqualities S U V lhs rhs heq
  obtain ⟨Q, hLQ, hPQ⟩ := exists_ge_ge L P
  let hQ := hL.trans hLQ
  have eqQ (k : Option Bool) := diagramNativeEq_trans S hL hLQ (hLeq k)
  have isoQ (k : Option Bool) : IsIso ((S.T hQ).map (u k)) := by
    let _ := hPiso k
    exact (NatIso.isIso_map_iff (S.assoc hP hPQ) (u k)).mp
      (inferInstanceAs (IsIso ((S.T hPQ).map ((S.T hP).map (u k)))))
  have : IsIso ((S.T hQ).map (u none)) := isoQ none
  have : IsIso ((S.T hQ).map (u (some false))) := isoQ (some false)
  have : IsIso ((S.T hQ).map (u (some true))) := isoQ (some true)
  let q : (S.T hQ).mapTriangle.obj τJ ≅ (S.T hQ).mapTriangle.obj ρJ :=
    Triangle.isoMk _ _ (asIso ((S.T hQ).map (u none)))
      (asIso ((S.T hQ).map (u (some false)))) (asIso ((S.T hQ).map (u (some true))))
      (by simpa [lhs, rhs, Functor.mapTriangle, Triangle.mk] using eqQ none)
      (by simpa [lhs, rhs, Functor.mapTriangle, Triangle.mk] using eqQ (some false))
      (by
        have nat : (S.T hQ).map ((shiftFunctor (C J) (1 : ℤ)).map (u none)) ≫
            ((S.T hQ).commShiftIso (1 : ℤ)).hom.app ρJ.obj₁ =
          ((S.T hQ).commShiftIso (1 : ℤ)).hom.app τJ.obj₁ ≫
            (shiftFunctor (C Q) (1 : ℤ)).map ((S.T hQ).map (u none)) :=
          ((S.T hQ).commShiftIso (1 : ℤ)).hom.naturality (u none)
        dsimp only [Functor.mapTriangle, Triangle.mk, asIso_hom]
        rw [Category.assoc, ← nat, ← Category.assoc, ← Functor.map_comp]
        rw [show τJ.mor₃ ≫ (shiftFunctor (C J) (1 : ℤ)).map (u none) = lhs (some true) from rfl,
          eqQ (some true)]
        simp [rhs, Category.assoc])
  let c (σ : Triangle (C i)) :=
    ((Functor.mapTriangleIso (S.assoc hJ hQ)).symm.app σ) ≪≫
      (Functor.mapTriangleCompIso (S.T hJ) (S.T hQ)).app σ
  exact ⟨Q, hJ.trans hQ, ⟨c τ ≪≫ q ≪≫ (c ρ).symm⟩⟩

section DistinguishedLifting
variable [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]

private theorem diagramDistinguished_refine {i : I} (τ : Triangle (C i))
    (hd : CommonStageDistinguished S ((S.ι i).mapTriangle.obj τ)) :
    ∃ (j : I) (h : i ≤ j), (S.T h).mapTriangle.obj τ ∈ distTriang (C j) := by
  obtain ⟨k, σ, hσ, ⟨e⟩⟩ := hd
  obtain ⟨J, hi, hk⟩ := exists_ge_ge i k
  let eJ := (diagramTriangleStageIso S hi τ).symm ≪≫ e ≪≫
    diagramTriangleStageIso S hk σ
  obtain ⟨L, hL, ⟨q⟩⟩ := diagramTriangleIso_lift S _ _ eJ
  have hdist := (S.T hL).map_distinguished _ ((S.T hk).map_distinguished σ hσ)
  have hτ := isomorphic_distinguished _ hdist _ q
  let c := ((Functor.mapTriangleIso (S.assoc hi hL)).symm.app τ) ≪≫
    (Functor.mapTriangleCompIso (S.T hi) (S.T hL)).app τ
  exact ⟨L, hi.trans hL, isomorphic_distinguished _ hτ _ c⟩

private theorem diagramRows_refine {A : Type a} {B : Type b} {R : Type r} [Finite R]
    (X : A → S.PairCategory) (s t : B → Vertex A)
    {M : I} (h : ∀ j, (X j).stage ≤ M)
    (u : ∀ j, (diagramVertex S X (s j)).toStage (h (s j).index) ⟶
      (diagramVertex S X (t j)).toStage (h (t j).index))
    (rows : R → Row s t)
    (hd : ∀ r, CommonStageDistinguished S ((S.ι M).mapTriangle.obj
      ((rows r).triangle (fun x ↦ (diagramVertex S X x).toStage (h x.index))
        (diagramSigma S X h) u))) :
    ∃ (N : I) (k : M ≤ N), ∀ r,
      (rows r).triangle (fun x ↦ (diagramVertex S X x).toStage ((h x.index).trans k))
        (diagramSigma S X (fun j ↦ (h j).trans k)) (fun j ↦ S.tr k (u j)) ∈
          distTriang (C N) := by
  classical
  choose k hk hd using fun r ↦ diagramDistinguished_refine S _ (hd r)
  obtain ⟨N, hN⟩ := Finite.exists_le (fun r : Option R ↦ r.elim M k)
  refine ⟨N, hN none, fun r ↦ ?_⟩
  have hKr : k r ≤ N := hN (some r)
  have H := (S.T hKr).map_distinguished _ (hd r)
  let τ := (rows r).triangle
    (fun x ↦ (diagramVertex S X x).toStage (h x.index)) (diagramSigma S X h) u
  let c := ((Functor.mapTriangleIso (S.assoc (hk r) hKr)).symm.app τ) ≪≫
    (Functor.mapTriangleCompIso (S.T (hk r)) (S.T hKr)).app τ
  exact isomorphic_distinguished _ H _
    (diagramRow_transportIso S X s t h (hN none) u (rows r) ≪≫ c)

end DistinguishedLifting

private theorem diagramRecovery {X Y : S.PairCategory} {M : I}
    (hX : X.stage ≤ M) (hY : Y.stage ≤ M) (u : X.toStage hX ⟶ Y.toStage hY) :
    (S.isoToStage X hX).hom ≫ (S.ι M).map u =
      PairCategory.mkHom M hX hY u ≫ (S.isoToStage Y hY).hom := by
  simp only [mkHom_eq_isoToStage, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem diagramShiftRecovery (X : S.PairCategory) {M : I} (h : X.stage ≤ M) :
    (S.isoToStage ((pbcPairShift S (1 : ℤ)).obj X) h).hom ≫
        (S.ι M).map (((S.T h).commShiftIso (1 : ℤ)).hom.app X.obj) ≫
        ((S.ι M).commShiftIso (1 : ℤ)).hom.app _ =
      (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X h).hom := by
  cases X with
  | mk i K =>
    let _ := diagramTransIsoCommShift S h
    have eq := (NatTrans.shift_app_comm (S.transIso h).inv (1 : ℤ) K).symm
    simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      transIso_inv_app, diagramInclusionShift, Category.id_comp, pbcPairShift,
      Morphism.functor_obj, pbcStageShift] using eq



private theorem diagramRowIso {A : Type a} {B : Type b}
    (X : A → S.PairCategory) (s t : B → Vertex A)
    (f : ∀ k, diagramVertex S X (s k) ⟶ diagramVertex S X (t k))
    {M : I} (h : ∀ j, (X j).stage ≤ M)
    (u : ∀ k, (diagramVertex S X (s k)).toStage (h (s k).index) ⟶
      (diagramVertex S X (t k)).toStage (h (t k).index))
    (hu : ∀ k, PairCategory.mkHom (X := diagramVertex S X (s k))
      (Y := diagramVertex S X (t k)) M (h (s k).index) (h (t k).index) (u k) = f k)
    (R : Row s t) :
    ∃ q : R.triangle (diagramVertex S X) (diagramPairSigma S X) f ≅
        (S.ι M).mapTriangle.obj
          (R.triangle (fun x ↦ (diagramVertex S X x).toStage (h x.index))
            (diagramSigma S X h) u),
      q.hom.hom₁ = (S.isoToStage (diagramVertex S X R.first) (h R.first.index)).hom ∧
      q.hom.hom₂ = (S.isoToStage (diagramVertex S X R.second) (h R.second.index)).hom ∧
      q.hom.hom₃ = (S.isoToStage (diagramVertex S X R.third) (h R.third.index)).hom := by
  have hr {x y : Vertex A} (p : Expr s t x y) :=
    (diagramRecovery S (X := diagramVertex S X x) (Y := diagramVertex S X y) (h x.index) (h y.index)
      (p.eval (fun x ↦ (diagramVertex S X x).toStage (h x.index))
        (diagramSigma S X h) u)).trans
      (congrArg (· ≫ (S.isoToStage (diagramVertex S X y) (h y.index)).hom)
        (diagramExpr_represents S X s t f h u hu p))
  refine ⟨Triangle.isoMk _ _ (S.isoToStage (diagramVertex S X R.first) (h R.first.index))
    (S.isoToStage (diagramVertex S X R.second) (h R.second.index))
    (S.isoToStage (diagramVertex S X R.third) (h R.third.index))
    (hr R.f).symm (hr R.i).symm ?_, rfl, rfl, rfl⟩
  simp only [Row.triangle, Functor.mapTriangle, Triangle.mk,
    diagramPairSigma, Iso.refl_hom, Category.comp_id]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← diagramShiftRecovery S (diagramVertex S X R.first) (h R.first.index)]
  rw [← Category.assoc]
  erw [← hr R.p]
  simp only [Category.assoc]
  rfl


private abbrev diagramStageVertex {A : Type a} (X : A → S.PairCategory)
    (M : I) (h : ∀ j, (X j).stage ≤ M) (x : Vertex A) : C M :=
  (diagramVertex S X x).toStage (h x.index)

private abbrev diagramStageShift {A : Type a} (X : A → S.PairCategory)
    (M : I) (h : ∀ j, (X j).stage ≤ M) (x : Vertex A) := diagramSigma S X h x

private abbrev diagramVertexIso {A : Type a} (X : A → S.PairCategory)
    (M : I) (h : ∀ j, (X j).stage ≤ M) (x : Vertex A) :=
  S.isoToStage (diagramVertex S X x) (h x.index)

section
variable [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]

private theorem diagramLifting
    {A : Type a} {B : Type b} {J : Type e} {R : Type r}
    [Finite A] [Finite B] [Finite J] [Finite R]
    (X : A → S.PairCategory)
    (s t : B → Vertex A)
    (f : ∀ k : B, diagramVertex S X (s k) ⟶ diagramVertex S X (t k))
    (eqs : J → Equation s t) (rows : R → Row s t)
    (heqs : ∀ j : J,
      (eqs j).lhs.eval (diagramVertex S X) (diagramPairSigma S X) f =
        (eqs j).rhs.eval (diagramVertex S X) (diagramPairSigma S X) f)
    (hrows : ∀ k : R, CommonStageDistinguished S
      ((rows k).triangle (diagramVertex S X) (diagramPairSigma S X) f))
    (M0 : I) :
    ∃ (M : I) (_ : M0 ≤ M)
      (h : ∀ j : A, (X j).stage ≤ M)
      (u : ∀ k : B, diagramStageVertex S X M h (s k) ⟶
        diagramStageVertex S X M h (t k)),
      (∀ (x y : Vertex A) (p : Expr s t x y),
        PairCategory.mkHom (X := diagramVertex S X x)
          (Y := diagramVertex S X y) M (h x.index) (h y.index)
          (p.eval (diagramStageVertex S X M h) (diagramStageShift S X M h) u) =
        p.eval (diagramVertex S X) (diagramPairSigma S X) f) ∧
      (∀ j : J,
        (eqs j).lhs.eval (diagramStageVertex S X M h)
            (diagramStageShift S X M h) u =
          (eqs j).rhs.eval (diagramStageVertex S X M h)
            (diagramStageShift S X M h) u) ∧
      (∀ k : R,
        (rows k).triangle (diagramStageVertex S X M h)
            (diagramStageShift S X M h) u ∈ distTriang (C M)) ∧
      (∀ (x y : Vertex A) (p : Expr s t x y),
        (diagramVertexIso S X M h x).hom ≫
            (S.ι M).map
              (p.eval (diagramStageVertex S X M h)
                (diagramStageShift S X M h) u) =
          p.eval (diagramVertex S X) (diagramPairSigma S X) f ≫
            (diagramVertexIso S X M h y).hom) ∧
      (∀ k : R, ∃ q :
        (rows k).triangle (diagramVertex S X) (diagramPairSigma S X) f ≅
          (S.ι M).mapTriangle.obj
            ((rows k).triangle (diagramStageVertex S X M h)
              (diagramStageShift S X M h) u),
        q.hom.hom₁ = (diagramVertexIso S X M h (rows k).first).hom ∧
        q.hom.hom₂ = (diagramVertexIso S X M h (rows k).second).hom ∧
        q.hom.hom₃ = (diagramVertexIso S X M h (rows k).third).hom) := by
  classical
  choose k hX hY hk using fun b ↦ PairCategory.exists_mkHom_eq (f b)
  obtain ⟨L, hL⟩ := Finite.exists_le (fun z : Option (A ⊕ B) ↦
    z.elim M0 (Sum.elim (fun a ↦ (X a).stage) k))
  let h : ∀ a, (X a).stage ≤ L := fun a ↦ hL (some (Sum.inl a))
  choose u hu using fun b ↦ hk b L (hL (some (Sum.inr b)))
  have hu' (b : B) : PairCategory.mkHom
      (X := diagramVertex S X (s b)) (Y := diagramVertex S X (t b))
      L (h (s b).index) (h (t b).index) (u b) = f b := (hu b).symm
  have hrep {x y : Vertex A} (p : Expr s t x y) :=
    diagramExpr_represents S X s t f h u hu' p
  let V := fun x ↦ diagramStageVertex S X L h x
  let sigma := diagramStageShift S X L h
  have he (j : J) : PairCategory.mkHom
      (X := diagramVertex S X (eqs j).source)
      (Y := diagramVertex S X (eqs j).target)
      L (h (eqs j).source.index) (h (eqs j).target.index) ((eqs j).lhs.eval V sigma u) =
      PairCategory.mkHom (X := diagramVertex S X (eqs j).source)
        (Y := diagramVertex S X (eqs j).target)
        L (h (eqs j).source.index) (h (eqs j).target.index)
        ((eqs j).rhs.eval V sigma u) :=
    (hrep (eqs j).lhs).trans ((heqs j).trans (hrep (eqs j).rhs).symm)
  choose N hN eN using fun j ↦ diagramEq_refine S _ _ (he j)
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun j : Option J ↦ j.elim L N)
  let h' : ∀ a, (X a).stage ≤ Q := fun a ↦ (h a).trans (hQ none)
  let u' := fun b ↦ S.tr (hQ none) (u b)
  have hu'' (b : B) : PairCategory.mkHom
      (X := diagramVertex S X (s b)) (Y := diagramVertex S X (t b))
      Q (h' (s b).index) (h' (t b).index) (u' b) = f b :=
    (PairCategory.mkHom_tr (hQ none) (u b)).trans (hu' b)
  have he' (j : J) :
      (eqs j).lhs.eval (diagramStageVertex S X Q h')
          (diagramStageShift S X Q h') u' =
        (eqs j).rhs.eval (diagramStageVertex S X Q h')
          (diagramStageShift S X Q h') u' := by
    have eq := congrArg (S.tr (hQ (some j))) (eN j)
    have eq' : S.tr (hQ none) ((eqs j).lhs.eval V sigma u) =
        S.tr (hQ none) ((eqs j).rhs.eval V sigma u) := by
      simpa only [tr_tr] using eq
    exact (diagramExpr_transport S X s t h (hQ none) u (eqs j).lhs).symm.trans
      (eq'.trans (diagramExpr_transport S X s t h (hQ none) u (eqs j).rhs))
  have hd (r : R) : CommonStageDistinguished S ((S.ι Q).mapTriangle.obj
      ((rows r).triangle (diagramStageVertex S X Q h')
        (diagramStageShift S X Q h') u')) := by
    obtain ⟨q, _⟩ := diagramRowIso S X s t f h' u' hu'' (rows r)
    obtain ⟨i, τ, hτ, ⟨e⟩⟩ := hrows r
    exact ⟨i, τ, hτ, ⟨q.symm ≪≫ e⟩⟩
  obtain ⟨M, hM, hdM⟩ := diagramRows_refine S X s t h' u' rows hd
  let hM' : ∀ a, (X a).stage ≤ M := fun a ↦ (h' a).trans hM
  let uM := fun b ↦ S.tr hM (u' b)
  have huM (b : B) : PairCategory.mkHom
      (X := diagramVertex S X (s b)) (Y := diagramVertex S X (t b))
      M (hM' (s b).index) (hM' (t b).index) (uM b) = f b :=
    (PairCategory.mkHom_tr hM (u' b)).trans (hu'' b)
  have hrepM {x y : Vertex A} (p : Expr s t x y) :=
    diagramExpr_represents S X s t f hM' uM huM p
  refine ⟨M, (hL none).trans ((hQ none).trans hM), hM', uM,
    fun x y p ↦ hrepM p, ?_, hdM, ?_, ?_⟩
  · intro j
    have eq := congrArg (S.tr hM) (he' j)
    exact (diagramExpr_transport S X s t h' hM u' (eqs j).lhs).symm.trans
      (eq.trans (diagramExpr_transport S X s t h' hM u' (eqs j).rhs))
  · intro x y p
    exact (diagramRecovery S (X := diagramVertex S X x)
      (Y := diagramVertex S X y) (hM' x.index) (hM' y.index) _).trans
        (congrArg (· ≫ (diagramVertexIso S X M hM' y).hom) (hrepM p))
  · intro r
    exact diagramRowIso S X s t f hM' uM huM (rows r)

end

end DiagramLifting
end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

open CategoryTheory.PbcFiniteDiagram CategoryTheory.StageSystem

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The occurrence (E,K[n]) uses the original vertex's field, with no fresh object choice.
Source: blueprint vertex sharing (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertex {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out) (x : Vertex A) :
    PbcFiniteStagePairCategory l Ω T hDim.out hInv.out :=
  ⟨(X x.index).stage, iterShift (X x.index).obj x.shifts⟩

/-- The pair shift is literal on these occurrences. Source: blueprint common-stage shift
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertexShift {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out) (x : Vertex A) :
    pbcDiagramVertex l Ω T X x.shift ≅ (pbcDiagramVertex l Ω T X x)⟦(1 : ℤ)⟧ :=
  Iso.refl _

/-- The raw lift is T_(M/E)(K[n]), shared at every occurrence. Source: blueprint raw
representatives (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
abbrev pbcDiagramStageVertex {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) : pbcStageCategory l Ω T M :=
  (pbcDiagramVertex l Ω T X x).toStage (h x.index)

/-- The actual transition sigma, with its already prescribed normalization and coherence.
Source: blueprint scalar-extension comparisons
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramStageShift {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) :
    pbcDiagramStageVertex l Ω T X M h x.shift ≅
      (pbcDiagramStageVertex l Ω T X M h x)⟦(1 : ℤ)⟧ :=
  ((pbcScalarSystem l Ω T hDim.out hInv.out).T (h x.index)).commShiftIso
    (1 : ℤ) |>.app (iterShift (X x.index).obj x.shifts)

/-- Iterating the same sigma identifies the raw lift with the iterated shift of X_M.
Source: blueprint iterated sigma (blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramIteratedSigma {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (j : A) : ∀ n : ℕ,
      pbcDiagramStageVertex l Ω T X M h ⟨j, n⟩ ≅
        iterShift ((X j).toStage (h j)) n
  | 0 => Iso.refl _
  | n + 1 => pbcDiagramStageShift l Ω T X M h ⟨j, n⟩ ≪≫
      (shiftFunctor (pbcStageCategory l Ω T M) (1 : ℤ)).mapIso
        (pbcDiagramIteratedSigma X M h j n)

/-- Canonical vertex recovery, represented by the identity after normalized unit
identifications. Source: blueprint final recovery clause
(blueprint: lem-weil-pbc-distinguished-diagram-lifting). -/
def pbcDiagramVertexIso {A : Type a}
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (M : Padic.FiniteCoefficientFields l Ω) (h : ∀ j : A, (X j).stage ≤ M)
    (x : Vertex A) :
    pbcDiagramVertex l Ω T X x ≅
      ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).obj
        (pbcDiagramStageVertex l Ω T X M h x) :=
  (pbcScalarSystem l Ω T hDim.out hInv.out).isoToStage
    (pbcDiagramVertex l Ω T X x) (h x.index)

/-- Every finite configuration, including distinguished rows, descends simultaneously.
Source: blueprint main-20261015, thm-weil-pbc-verdier-axioms proof, TR2--TR4
(blueprint: lem-weil-pbc-distinguished-diagram-lifting).

Proof: (1) For each distinguished row, use common-stage distinguishedness to choose
an image distinguished triangle and a triangle isomorphism. Add its three components,
inverses, six inverse identities and three commuting equations to the finite data.
(2) Choose representatives for all arrows, retaining the chosen witness representatives.
Take a compositum containing their fields, the vertex and witness fields, and M0.
Transport by the associators; repeated vertices use the same scalar extension.
(3) Induct on the finite expressions. Composition, identities, addition, negatives and
zero commute with transport by commonStageCalculus. For shift the representative is
sigma_X followed by u[1] followed by sigma_Y inverse; iterating gives repeated shifts.
Use eventual equality for each true equation, then a compositum of their finitely many
witness fields, to make every equation hold simultaneously.
(4) Exact scalar extension takes each witness triangle to a distinguished triangle.
Associator/shift coherence identifies its last arrow with the transported raw arrow
followed by sigma, so the corrected witness row is distinguished at the final stage.
(5) The transported inverse equations and triangle squares make each witness isomorphism
an isomorphism of stage triangles; finite-stage TR1 gives every selected row.
(6) The canonical isoToStage maps recover every arrow and term. On a vertex their
representatives are identities after the normalized units; the shift formula gives
recovery of the corrected last arrows and all iterated shifted arrows. Empty finite
families only require the prescribed base stage. No Verdier axiom on the pair category
is used. -/
theorem pbcDistinguishedDiagramLifting
    {A : Type a} {B : Type b} {J : Type e} {R : Type r}
    [Finite A] [Finite B] [Finite J] [Finite R]
    (X : A → PbcFiniteStagePairCategory l Ω T hDim.out hInv.out)
    (s t : B → Vertex A)
    (f : ∀ k : B, pbcDiagramVertex l Ω T X (s k) ⟶ pbcDiagramVertex l Ω T X (t k))
    (eqs : J → Equation s t) (rows : R → Row s t)
    (heqs : ∀ j : J,
      (eqs j).lhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f =
        (eqs j).rhs.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f)
    (hrows : ∀ k : R, pbcCommonStageDistinguished l Ω T
      ((rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f))
    (M0 : Padic.FiniteCoefficientFields l Ω) :
    ∃ (M : Padic.FiniteCoefficientFields l Ω) (_ : M0 ≤ M)
      (h : ∀ j : A, (X j).stage ≤ M)
      (u : ∀ k : B, pbcDiagramStageVertex l Ω T X M h (s k) ⟶
        pbcDiagramStageVertex l Ω T X M h (t k)),
      (∀ (x y : Vertex A) (p : Expr s t x y),
        PairCategory.mkHom (X := pbcDiagramVertex l Ω T X x)
          (Y := pbcDiagramVertex l Ω T X y) M (h x.index) (h y.index)
          (p.eval (pbcDiagramStageVertex l Ω T X M h) (pbcDiagramStageShift l Ω T X M h) u) =
        p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f) ∧
      (∀ j : J,
        (eqs j).lhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u =
          (eqs j).rhs.eval (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u) ∧
      (∀ k : R,
        (rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
            (pbcDiagramStageShift l Ω T X M h) u ∈ distTriang (pbcStageCategory l Ω T M)) ∧
      (∀ (x y : Vertex A) (p : Expr s t x y),
        (pbcDiagramVertexIso l Ω T X M h x).hom ≫
            ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).map
              (p.eval (pbcDiagramStageVertex l Ω T X M h)
                (pbcDiagramStageShift l Ω T X M h) u) =
          p.eval (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≫
            (pbcDiagramVertexIso l Ω T X M h y).hom) ∧
      (∀ k : R, ∃ q :
        (rows k).triangle (pbcDiagramVertex l Ω T X) (pbcDiagramVertexShift l Ω T X) f ≅
          ((pbcScalarSystem l Ω T hDim.out hInv.out).ι M).mapTriangle.obj
            ((rows k).triangle (pbcDiagramStageVertex l Ω T X M h)
              (pbcDiagramStageShift l Ω T X M h) u),
        q.hom.hom₁ = (pbcDiagramVertexIso l Ω T X M h (rows k).first).hom ∧
        q.hom.hom₂ = (pbcDiagramVertexIso l Ω T X M h (rows k).second).hom ∧
        q.hom.hom₃ = (pbcDiagramVertexIso l Ω T X M h (rows k).third).hom) := by
  exact diagramLifting (pbcScalarSystem l Ω T hDim.out hInv.out)
    X s t f eqs rows heqs hrows M0

end AlgebraicGeometry.Scheme
