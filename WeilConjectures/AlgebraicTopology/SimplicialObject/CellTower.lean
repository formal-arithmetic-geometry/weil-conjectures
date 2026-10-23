/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.AttachCells
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Split simplicial objects built by attaching cells degree by degree

Let `C` be a category with finite coproducts and `Y` a simplicial object in `C`. Given, for
every `m : ℕ` and every simplicial object `W` with a map `ℓ : W ⟶ Y`, a way of attaching new
nondegenerate `m`-simplices to `W` over `Y` (`SimplicialObject.AttachStep`), we construct
inductively simplicial objects `CellTower.obj step m` (with cells in degrees `< m`), starting
from the initial simplicial object, and their colimit `CellTower.W step`. The colimit is a
split simplicial object (`CellTower.splitting`) whose nondegenerate `m`-simplices are the cells
attached in degree `m`, and it comes with a map `CellTower.toY step : W step ⟶ Y`.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace BoundaryCone

variable {W : SimplicialObject C} {n : ℕ} {N : C}

lemma postcomp_postcomp (c : BoundaryCone W n N) {W' W'' : SimplicialObject C} (g : W ⟶ W')
    (g' : W' ⟶ W'') : (c.postcomp g).postcomp g' = c.postcomp (g ≫ g') :=
  ext' fun _ _ _ ↦ by simp

lemma ofSimplex_postcomp (f : N ⟶ W _⦋n⦌) {W' : SimplicialObject C} (g : W ⟶ W') :
    (BoundaryCone.ofSimplex f).postcomp g = BoundaryCone.ofSimplex (f ≫ g.app _) :=
  ext' fun _ _ _ ↦ by simp

lemma precomp_precomp (c : BoundaryCone W n N) {N' N'' : C} (f : N' ⟶ N) (f' : N'' ⟶ N') :
    (c.precomp f).precomp f' = c.precomp (f' ≫ f) :=
  ext' fun _ _ _ ↦ by simp

lemma precomp_postcomp (c : BoundaryCone W n N) {N' : C} (f : N' ⟶ N)
    {W' : SimplicialObject C} (g : W ⟶ W') :
    (c.precomp f).postcomp g = (c.postcomp g).precomp f :=
  ext' fun _ _ _ ↦ by simp

lemma ofSimplex_precomp (s : N ⟶ W _⦋n⦌) {N' : C} (f : N' ⟶ N) :
    (BoundaryCone.ofSimplex s).precomp f = BoundaryCone.ofSimplex (f ≫ s) :=
  ext' fun _ _ _ ↦ by simp

end BoundaryCone

/-- The data needed to attach new nondegenerate `m`-simplices to `W`, compatibly with a map
`ℓ : W ⟶ Y`: an object `N` of new simplices, their boundary (a boundary cone), and their images
in `Y`. -/
structure AttachStep {W Y : SimplicialObject C} (ℓ : W ⟶ Y) (m : ℕ) where
  /-- The object of new nondegenerate `m`-simplices. -/
  N : C
  /-- The boundary of the new simplices. -/
  cone : BoundaryCone W m N
  /-- The images of the new simplices in `Y`. -/
  lift : N ⟶ Y _⦋m⦌
  fac : cone.postcomp ℓ = BoundaryCone.ofSimplex lift

variable [HasFiniteCoproducts C]

namespace CellTower

variable {Y : SimplicialObject C}
  (step : ∀ (m : ℕ) (W : SimplicialObject C) (ℓ : W ⟶ Y), AttachStep ℓ m)

/-- The initial simplicial object. -/
abbrev initialObj : SimplicialObject C := (Functor.const _).obj (⊥_ C)

/-- The map from the initial simplicial object. -/
def initialTo (Y : SimplicialObject C) : (initialObj : SimplicialObject C) ⟶ Y where
  app _ := initial.to _
  naturality _ _ _ := initial.hom_ext _ _

/-- The stages of the construction: the simplicial object obtained after attaching cells in
degrees `< m`, with its map to `Y`. -/
def stage : ℕ → Σ W : SimplicialObject C, (W ⟶ Y)
  | 0 => ⟨initialObj, initialTo Y⟩
  | m + 1 =>
    ⟨(step m (stage m).1 (stage m).2).cone.attach,
      (step m (stage m).1 (stage m).2).cone.attachDesc (stage m).2
        (step m (stage m).1 (stage m).2).lift (step m (stage m).1 (stage m).2).fac⟩

/-- The `m`-th stage. -/
abbrev obj (m : ℕ) : SimplicialObject C := (stage step m).1

/-- The map from the `m`-th stage to `Y`. -/
abbrev objToY (m : ℕ) : obj step m ⟶ Y := (stage step m).2

/-- The data used to attach the cells of degree `m`. -/
abbrev cells (m : ℕ) : AttachStep (objToY step m) m := step m (obj step m) (objToY step m)

lemma obj_zero : obj step 0 = initialObj := rfl

lemma obj_succ (m : ℕ) : obj step (m + 1) = (cells step m).cone.attach := rfl

lemma objToY_succ (m : ℕ) : objToY step (m + 1) =
    (cells step m).cone.attachDesc (objToY step m) (cells step m).lift (cells step m).fac :=
  rfl

/-- The tower of stages. -/
def tower : ℕ ⥤ SimplicialObject C :=
  Functor.ofSequence (X := obj step) fun m ↦ (cells step m).cone.attachInl

@[simp]
lemma tower_obj (m : ℕ) : (tower step).obj m = obj step m := rfl

lemma tower_map_succ (m : ℕ) :
    (tower step).map (homOfLE (Nat.le_succ m)) = (cells step m).cone.attachInl :=
  Functor.ofSequence_map_homOfLE_succ _ m

lemma tower_map_comp {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    (tower step).map (homOfLE (h₁.trans h₂)) =
      (tower step).map (homOfLE h₁) ≫ (tower step).map (homOfLE h₂) := by
  rw [← Functor.map_comp]
  rfl

lemma tower_map_refl (i : ℕ) (h : i ≤ i) : (tower step).map (homOfLE h) = 𝟙 _ :=
  (tower step).map_id i

lemma isIso_tower_map_app (k : SimplexCategoryᵒᵖ) {i j : ℕ} (hij : i ≤ j)
    (hi : k.unop.len < i) : IsIso (((tower step).map (homOfLE hij)).app k) := by
  induction j, hij using Nat.le_induction with
  | base =>
    rw [tower_map_refl]
    exact inferInstanceAs (IsIso (𝟙 _))
  | succ j hij ih =>
    rw [tower_map_comp step hij (Nat.le_succ j), NatTrans.comp_app, tower_map_succ]
    have := (cells step j).cone.isIso_attachInl_app k (by omega)
    infer_instance

lemma isEventuallyConstantFrom (k : SimplexCategoryᵒᵖ) :
    (tower step ⋙ (evaluation _ _).obj k).IsEventuallyConstantFrom (k.unop.len + 1) :=
  fun _ f ↦ isIso_tower_map_app step k (leOfHom f) (Nat.lt_succ_self _)

instance (k : SimplexCategoryᵒᵖ) : HasColimit ((tower step).flip.obj k) :=
  (isEventuallyConstantFrom step k).hasColimit

/-- The colimit of the tower of stages. -/
def W : SimplicialObject C := colimit (tower step)

/-- The map from the `m`-th stage to the colimit. -/
def ι (m : ℕ) : obj step m ⟶ W step := colimit.ι (tower step) m

lemma attachInl_ι (m : ℕ) : (cells step m).cone.attachInl ≫ ι step (m + 1) = ι step m := by
  have := colimit.w (tower step) (homOfLE (Nat.le_succ m))
  rwa [tower_map_succ] at this

lemma tower_map_ι {i j : ℕ} (hij : i ≤ j) :
    (tower step).map (homOfLE hij) ≫ ι step j = ι step i :=
  colimit.w (tower step) (homOfLE hij)

lemma isIso_ι_app (m : ℕ) (k : SimplexCategoryᵒᵖ) (hk : k.unop.len < m) :
    IsIso ((ι step m).app k) :=
  (isEventuallyConstantFrom step k).isIso_ι_of_isColimit'
    (isColimitOfPreserves ((evaluation _ _).obj k) (colimit.isColimit _)) m (homOfLE hk)

/-- The map from the colimit to `Y`. -/
def toY : W step ⟶ Y :=
  colimit.desc (tower step) (Cocone.mk Y (NatTrans.ofSequence (objToY step) fun m ↦ by
    simp only [tower_map_succ, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [objToY_succ]
    exact (cells step m).cone.attachInl_attachDesc _ _ _))

@[reassoc (attr := simp)]
lemma ι_toY (m : ℕ) : ι step m ≫ toY step = objToY step m :=
  colimit.ι_desc _ _

/-- The new nondegenerate simplices of degree `m` of the colimit. -/
def N (m : ℕ) : C := (cells step m).N

/-- The inclusion of the new nondegenerate simplices of degree `m` into the colimit. -/
def cellι (m : ℕ) : N step m ⟶ (W step) _⦋m⦌ :=
  (cells step m).cone.attachι ≫ (ι step (m + 1)).app _

lemma ofSimplex_cellι (m : ℕ) :
    BoundaryCone.ofSimplex (cellι step m) = (cells step m).cone.postcomp (ι step m) := by
  rw [cellι, ← BoundaryCone.ofSimplex_postcomp, ← BoundaryCone.postcomp_attachInl_eq,
    BoundaryCone.postcomp_postcomp, attachInl_ι]

@[reassoc (attr := simp)]
lemma cellι_toY_app (m : ℕ) : cellι step m ≫ (toY step).app _ = (cells step m).lift := by
  rw [cellι, Category.assoc, ← NatTrans.comp_app, ι_toY, objToY_succ,
    BoundaryCone.attachι_attachDesc_app]

/-- The summand inclusions of the `m`-th stage in degree `Δ`, indexed by the elements of
`Splitting.IndexSet Δ` of dimension `< m`. -/
def stageInj (m : ℕ) (Δ : SimplexCategoryᵒᵖ)
    (A : {A : Splitting.IndexSet Δ // A.1.unop.len < m}) :
    N step A.1.1.unop.len ⟶ (obj step m).obj Δ :=
  (cells step A.1.1.unop.len).cone.attachι ≫
    ((tower step).map (homOfLE (Nat.succ_le_of_lt A.2))).app _ ≫ (obj step m).map A.1.e.op

lemma stageInj_succ_of_lt (m : ℕ) (Δ : SimplexCategoryᵒᵖ) (A : Splitting.IndexSet Δ)
    (hA : A.1.unop.len < m) :
    stageInj step (m + 1) Δ ⟨A, Nat.lt_succ_of_lt hA⟩ =
      stageInj step m Δ ⟨A, hA⟩ ≫ (cells step m).cone.attachInl.app Δ := by
  simp only [stageInj, Category.assoc]
  rw [(cells step m).cone.attachInl.naturality,
    tower_map_comp step (Nat.succ_le_of_lt hA) (Nat.le_succ m), NatTrans.comp_app,
    tower_map_succ, Category.assoc]
  rfl

lemma stageInj_succ_mk (m : ℕ) (Δ : SimplexCategoryᵒᵖ) (s : Δ.unop ⟶ ⦋m⦌) [Epi s] :
    stageInj step (m + 1) Δ ⟨Splitting.IndexSet.mk s, Nat.lt_succ_self m⟩ =
      Sigma.ι (fun _ : Δ.unop ⟶ ⦋m⦌ ↦ (cells step m).N) s ≫
        (cells step m).cone.attachInr.app Δ := by
  rw [BoundaryCone.ι_attachInr_app]
  change (cells step m).cone.attachι ≫ ((tower step).map (homOfLE (le_refl (m + 1)))).app _ ≫
    (obj step (m + 1)).map s.op = _
  rw [tower_map_refl, NatTrans.id_app]
  erw [Category.id_comp]
  rfl

/-- The `m`-th stage is, in each degree `Δ`, the coproduct of the cells of dimension `< m`
indexed by `Splitting.IndexSet Δ`. -/
def isColimitStage (Δ : SimplexCategoryᵒᵖ) :
    ∀ m : ℕ, IsColimit (Cofan.mk ((obj step m).obj Δ) (stageInj step m Δ))
  | 0 => Cofan.IsColimit.mk _ (fun _ ↦ initial.to _)
      (fun _ A ↦ absurd A.2 (Nat.not_lt_zero _)) (fun _ _ _ ↦ initial.hom_ext _ _)
  | m + 1 => by
    let hb := (cells step m).cone.isColimitAttachBinaryCofan Δ
    let ih := isColimitStage Δ m
    refine Cofan.IsColimit.mk _
      (fun t ↦ hb.desc (BinaryCofan.mk
        (ih.desc (Cofan.mk t.pt fun A ↦ t.inj ⟨A.1, Nat.lt_succ_of_lt A.2⟩))
        (Sigma.desc fun s : {s : Δ.unop ⟶ ⦋m⦌ // Epi s} ↦
          t.inj ⟨⟨op ⦋m⦌, s.1, s.2⟩, Nat.lt_succ_self m⟩))) (fun t A ↦ ?_) (fun t g hg ↦ ?_)
    · obtain ⟨⟨⟨Δ'⟩, e, he⟩, hA⟩ := A
      rw [cofan_mk_inj]
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hA) with hA' | hA'
      · have := stageInj_succ_of_lt step m Δ ⟨⟨Δ'⟩, e, he⟩ hA'
        rw [this, Category.assoc]
        erw [hb.fac _ (.mk .left)]
        exact ih.fac _ ⟨⟨⟨⟨Δ'⟩, e, he⟩, hA'⟩⟩
      · obtain rfl : Δ' = ⦋m⦌ := SimplexCategory.ext hA'
        have := stageInj_succ_mk step m Δ e
        have h' : Sigma.ι (fun _ : Δ.unop ⟶ ⦋m⦌ ↦ (cells step m).N) e ≫
            (cells step m).cone.attachInr.app Δ =
            Sigma.ι (fun _ : {s : Δ.unop ⟶ ⦋m⦌ // Epi s} ↦ (cells step m).N) ⟨e, he⟩ ≫
              Sigma.desc (fun s : {s : Δ.unop ⟶ ⦋m⦌ // Epi s} ↦
                Sigma.ι (fun _ ↦ (cells step m).N) s.1 ≫ (cells step m).cone.attachInr.app Δ) :=
          by rw [Sigma.ι_desc]
        erw [this, h', Category.assoc, hb.fac _ (.mk .right)]
        exact Sigma.ι_desc (fun s : {s : Δ.unop ⟶ ⦋m⦌ // Epi s} ↦
          t.inj ⟨⟨op ⦋m⦌, s.1, s.2⟩, Nat.lt_succ_self m⟩) ⟨e, he⟩
    · refine BinaryCofan.IsColimit.hom_ext hb ?_ ?_
      · refine Cofan.IsColimit.hom_ext ih _ _ (fun A ↦ ?_)
        have h₁ := hg ⟨A.1, Nat.lt_succ_of_lt A.2⟩
        rw [cofan_mk_inj, stageInj_succ_of_lt step m Δ A.1 A.2, Category.assoc] at h₁
        rw [cofan_mk_inj]
        erw [h₁, hb.fac _ (.mk .left)]
        exact (ih.fac (Cofan.mk t.pt fun A ↦ t.inj ⟨A.1, Nat.lt_succ_of_lt A.2⟩) ⟨A⟩).symm
      · refine Sigma.hom_ext _ _ (fun s ↦ ?_)
        have := s.2
        have h₂ := hg ⟨Splitting.IndexSet.mk s.1, Nat.lt_succ_self m⟩
        rw [cofan_mk_inj, stageInj_succ_mk] at h₂
        erw [hb.fac _ (.mk .right)]
        rw [BinaryCofan.mk_inr, Sigma.ι_desc_assoc]
        erw [h₂]
        exact (Sigma.ι_desc (fun s : {s : Δ.unop ⟶ ⦋m⦌ // Epi s} ↦
          t.inj ⟨⟨op ⦋m⦌, s.1, s.2⟩, Nat.lt_succ_self m⟩) s).symm

/-- The colimit of the tower is split, with nondegenerate simplices the attached cells. -/
def splitting : Splitting (W step) where
  N := N step
  ι := cellι step
  isColimit' Δ := by
    have := isIso_ι_app step (Δ.unop.len + 1) Δ (Nat.lt_succ_self _)
    let h₁ := isColimitStage step Δ (Δ.unop.len + 1)
    let h₂ : IsColimit (Cofan.mk ((W step).obj Δ)
        fun A ↦ stageInj step (Δ.unop.len + 1) Δ A ≫ (ι step (Δ.unop.len + 1)).app Δ) :=
      IsColimit.ofIsoColimit h₁ (Cofan.ext (asIso ((ι step (Δ.unop.len + 1)).app Δ))
        (fun _ ↦ rfl))
    let e : {A : Splitting.IndexSet Δ // A.1.unop.len < Δ.unop.len + 1} ≃
        Splitting.IndexSet Δ :=
      Equiv.subtypeUnivEquiv fun A ↦ Nat.lt_succ_of_le (SimplexCategory.len_le_of_epi A.e)
    refine (Cofan.isColimitEquivOfEquiv (ε := e) _).symm
      (IsColimit.ofIsoColimit h₂ (Cofan.ext (Iso.refl _) (fun A ↦ ?_)))
    change (stageInj step (Δ.unop.len + 1) Δ A ≫ (ι step (Δ.unop.len + 1)).app Δ) ≫ 𝟙 _ =
      cellι step A.1.1.unop.len ≫ (W step).map A.1.e.op
    rw [Category.comp_id, stageInj, cellι, Category.assoc, Category.assoc, Category.assoc,
      (ι step _).naturality, ← NatTrans.comp_app_assoc, tower_map_ι]

@[simp]
lemma splitting_N (m : ℕ) : (splitting step).N m = N step m := rfl

@[simp]
lemma splitting_ι (m : ℕ) : (splitting step).ι m = cellι step m := rfl

end CellTower

end CategoryTheory.SimplicialObject
