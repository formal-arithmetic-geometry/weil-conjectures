/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Attaching nondegenerate simplices to a simplicial object

Let `C` be a category with finite coproducts. Given a simplicial object `W` in `C`, an
object `N` and a compatible family of maps from `N` to the lower-dimensional simplices of the
boundary of the `n`-simplex in `W` (`SimplicialObject.BoundaryCone`), we attach `N` as new
nondegenerate `n`-simplices to `W`: the attached object is the pushout of
`N ⊗ ∂Δ[n] ⟶ W` along `N ⊗ ∂Δ[n] ⟶ N ⊗ Δ[n]`, where `N ⊗ K` denotes the simplicial object
`Δ ↦ ∐_{K(Δ)} N` (`SimplicialObject.copow`). In each degree this pushout is the coproduct of
`W` with copies of `N` indexed by the surjections onto `⦋n⦌`.

This is the inductive step of the construction of split simplicial objects with prescribed
nondegenerate pieces (Stacks Project, Tag 017S), used to construct split hypercoverings.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section Copow

variable [HasFiniteCoproducts C]

/-- The copower `N ⊗ Δ[n]`: in degree `Δ` it is the coproduct of copies of `N` indexed by the
simplices `Δ ⟶ ⦋n⦌`. -/
@[simps]
abbrev stdCopow (N : C) (n : ℕ) : SimplicialObject C where
  obj Δ := ∐ fun _ : Δ.unop ⟶ ⦋n⦌ ↦ N
  map θ := Sigma.map' (fun s ↦ θ.unop ≫ s) (fun _ ↦ 𝟙 N)
  map_id Δ := by
    ext s
    simp
  map_comp θ θ' := by
    ext s
    simp

/-- The copower `N ⊗ ∂Δ[n]`: in degree `Δ` it is the coproduct of copies of `N` indexed by
the non-surjective simplices `Δ ⟶ ⦋n⦌`. -/
@[simps]
abbrev bdryCopow (N : C) (n : ℕ) : SimplicialObject C where
  obj Δ := ∐ fun _ : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s} ↦ N
  map θ := Sigma.map' (fun s ↦ ⟨θ.unop ≫ s.1, fun _ ↦ s.2 (epi_of_epi θ.unop s.1)⟩)
    (fun _ ↦ 𝟙 N)
  map_id Δ := by
    ext s
    simp
  map_comp θ θ' := by
    ext s
    simp

@[reassoc (attr := simp)]
lemma ι_stdCopow_map (N : C) (n : ℕ) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (s : Δ.unop ⟶ ⦋n⦌) :
    Sigma.ι (fun _ : Δ.unop ⟶ ⦋n⦌ ↦ N) s ≫ (stdCopow N n).map θ =
      Sigma.ι (fun _ : Δ'.unop ⟶ ⦋n⦌ ↦ N) (θ.unop ≫ s) := by
  simp [stdCopow]

@[reassoc (attr := simp)]
lemma ι_bdryCopow_map (N : C) (n : ℕ) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (s : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s}) :
    Sigma.ι (fun _ : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s} ↦ N) s ≫ (bdryCopow N n).map θ =
      Sigma.ι (fun _ : {s : Δ'.unop ⟶ ⦋n⦌ // ¬ Epi s} ↦ N)
        ⟨θ.unop ≫ s.1, fun _ ↦ s.2 (epi_of_epi θ.unop s.1)⟩ := by
  simp [bdryCopow]

/-- The inclusion `N ⊗ ∂Δ[n] ⟶ N ⊗ Δ[n]`. -/
@[simps]
def bdryIncl (N : C) (n : ℕ) : bdryCopow N n ⟶ stdCopow N n where
  app Δ := Sigma.map' Subtype.val (fun _ ↦ 𝟙 N)
  naturality Δ Δ' θ := by
    refine Sigma.hom_ext _ _ (fun s ↦ ?_)
    simp

@[reassoc (attr := simp)]
lemma ι_bdryIncl_app (N : C) (n : ℕ) (Δ : SimplexCategoryᵒᵖ)
    (s : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s}) :
    Sigma.ι (fun _ : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s} ↦ N) s ≫ (bdryIncl N n).app Δ =
      Sigma.ι (fun _ : Δ.unop ⟶ ⦋n⦌ ↦ N) s.1 := by
  simp

/-- A map `N ⟶ Y _⦋n⦌` induces a map `N ⊗ Δ[n] ⟶ Y`. -/
@[simps]
def copowStdDesc {N : C} {Y : SimplicialObject C} {n : ℕ} (f : N ⟶ Y _⦋n⦌) :
    stdCopow N n ⟶ Y where
  app Δ := Sigma.desc fun s ↦ f ≫ Y.map s.op
  naturality Δ Δ' θ := by
    refine Sigma.hom_ext _ _ (fun s ↦ ?_)
    simp only [ι_stdCopow_map_assoc, colimit.ι_desc, Cofan.mk_pt,
      Cofan.mk_ι_app, colimit.ι_desc_assoc, Category.assoc, ← Y.map_comp]
    rfl

@[reassoc (attr := simp)]
lemma ι_copowStdDesc_app {N : C} {Y : SimplicialObject C} {n : ℕ} (f : N ⟶ Y _⦋n⦌)
    (Δ : SimplexCategoryᵒᵖ) (s : Δ.unop ⟶ ⦋n⦌) :
    Sigma.ι (fun _ : Δ.unop ⟶ ⦋n⦌ ↦ N) s ≫ (copowStdDesc f).app Δ = f ≫ Y.map s.op := by
  simp

end Copow

/-- A compatible family of maps from `N` to the simplices of `W` lying on the boundary of the
`n`-simplex: a cone over the diagram defining the `n`-th matching object of `W`. -/
structure BoundaryCone (W : SimplicialObject C) (n : ℕ) (N : C) where
  /-- The component at a simplex `θ : Δ ⟶ ⦋n⦌` of dimension `< n`. -/
  π : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ ⦋n⦌) → (N ⟶ W.obj (op Δ))
  /-- Compatibility with the simplicial operators. -/
  w : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n) (α : Δ' ⟶ Δ)
    (θ : Δ ⟶ ⦋n⦌), π Δ h θ ≫ W.map α.op = π Δ' h' (α ≫ θ)

namespace BoundaryCone

variable {W : SimplicialObject C} {n : ℕ} {N : C}

/-- Precomposition of a boundary cone with a map. -/
@[simps]
def precomp (c : BoundaryCone W n N) {N' : C} (f : N' ⟶ N) : BoundaryCone W n N' where
  π Δ h θ := f ≫ c.π Δ h θ
  w Δ Δ' h h' α θ := by rw [Category.assoc, c.w]

/-- Postcomposition of a boundary cone with a map of simplicial objects. -/
@[simps]
def postcomp (c : BoundaryCone W n N) {W' : SimplicialObject C} (g : W ⟶ W') :
    BoundaryCone W' n N where
  π Δ h θ := c.π Δ h θ ≫ g.app (op Δ)
  w Δ Δ' h h' α θ := by
    rw [Category.assoc, ← g.naturality, ← Category.assoc, c.w]

/-- The boundary cone given by the faces of an `n`-simplex `f : N ⟶ W _⦋n⦌`. -/
@[simps]
def ofSimplex {n : ℕ} (f : N ⟶ W _⦋n⦌) : BoundaryCone W n N where
  π Δ _ θ := f ≫ W.map θ.op
  w Δ Δ' h h' α θ := by
    rw [Category.assoc, ← W.map_comp]
    rfl

lemma ext' {c d : BoundaryCone W n N} (h : ∀ Δ hΔ θ, c.π Δ hΔ θ = d.π Δ hΔ θ) : c = d := by
  cases c; cases d
  congr
  funext Δ hΔ θ
  exact h Δ hΔ θ

end BoundaryCone

lemma len_lt_of_mono_of_not_epi {Δ Δ' : SimplexCategory} {n : ℕ} {s : Δ ⟶ ⦋n⦌}
    (hs : ¬ Epi s) {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ ⦋n⦌} [Mono i] (fac : e ≫ i = s) :
    Δ'.len < n := by
  rcases (SimplexCategory.len_le_of_mono i).lt_or_eq with h | h
  · exact h
  · exfalso
    have : IsIso i := (SimplexCategory.isIso_iff_of_mono i).2 h
    exact hs (fac ▸ epi_comp e i)

section Attach

variable {W : SimplicialObject C} {n : ℕ} {N : C}

/-- The component of `BoundaryCone.desc` on the summand of a non-surjective simplex `s`. -/
def BoundaryCone.descApp (c : BoundaryCone W n N) {Δ : SimplexCategory} (s : Δ ⟶ ⦋n⦌)
    (hs : ¬ Epi s) : N ⟶ W.obj (op Δ) :=
  c.π (image s) (len_lt_of_mono_of_not_epi hs (image.fac s)) (image.ι s) ≫
    W.map (factorThruImage s).op

lemma BoundaryCone.descApp_eq (c : BoundaryCone W n N) {Δ Δ' : SimplexCategory}
    {s : Δ ⟶ ⦋n⦌} (hs : ¬ Epi s) {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ ⦋n⦌} [Mono i]
    (fac : e ≫ i = s) :
    c.descApp s hs = c.π Δ' (len_lt_of_mono_of_not_epi hs fac) i ≫ W.map e.op := by
  obtain rfl := SimplexCategory.image_eq fac
  simp only [descApp, SimplexCategory.image_ι_eq fac, SimplexCategory.factorThruImage_eq fac]

lemma BoundaryCone.descApp_comp (c : BoundaryCone W n N) {Δ Δ' : SimplexCategory}
    (s : Δ ⟶ ⦋n⦌) (hs : ¬ Epi s) (θ : Δ' ⟶ Δ) (hs' : ¬ Epi (θ ≫ s)) :
    c.descApp (θ ≫ s) hs' = c.descApp s hs ≫ W.map θ.op := by
  let t := θ ≫ factorThruImage s
  have hlt := len_lt_of_mono_of_not_epi hs (image.fac s)
  have fac : factorThruImage t ≫ (image.ι t ≫ image.ι s) = θ ≫ s := by
    rw [image.fac_assoc, Category.assoc, image.fac]
  have ht : θ ≫ factorThruImage s = factorThruImage t ≫ image.ι t := (image.fac t).symm
  rw [c.descApp_eq hs' fac, descApp, Category.assoc, ← W.map_comp, ← op_comp, ht, op_comp,
    W.map_comp, ← Category.assoc, c.w _ _ hlt]

lemma BoundaryCone.descApp_ofSimplex {Y : SimplicialObject C} (f : N ⟶ Y _⦋n⦌)
    {Δ : SimplexCategory} (s : Δ ⟶ ⦋n⦌) (hs : ¬ Epi s) :
    (BoundaryCone.ofSimplex f).descApp s hs = f ≫ Y.map s.op := by
  rw [descApp, ofSimplex_π, Category.assoc, ← Y.map_comp, ← op_comp, image.fac]

lemma BoundaryCone.descApp_postcomp (c : BoundaryCone W n N) {Y : SimplicialObject C}
    (g : W ⟶ Y) {Δ : SimplexCategory} (s : Δ ⟶ ⦋n⦌) (hs : ¬ Epi s) :
    (c.postcomp g).descApp s hs = c.descApp s hs ≫ g.app (op Δ) := by
  rw [descApp, descApp, postcomp_π, Category.assoc, Category.assoc, g.naturality]

lemma BoundaryCone.descApp_eq_π (c : BoundaryCone W n N) {Δ : SimplexCategory}
    (θ : Δ ⟶ ⦋n⦌) (hθ : ¬ Epi θ) (hΔ : Δ.len < n) : c.descApp θ hθ = c.π Δ hΔ θ := by
  rw [descApp, c.w _ _ _ hΔ, image.fac]

variable [HasFiniteCoproducts C]

/-- The map `N ⊗ ∂Δ[n] ⟶ W` induced by a boundary cone. On the summand of a non-surjective
simplex `s`, it is given using the epi-mono factorisation `s = e ≫ i` by `c.π _ _ i ≫ W.map e`. -/
@[simps]
def BoundaryCone.desc (c : BoundaryCone W n N) : bdryCopow N n ⟶ W where
  app Δ := Sigma.desc fun s ↦ c.descApp s.1 s.2
  naturality Δ Δ' θ := by
    refine Sigma.hom_ext _ _ (fun s ↦ ?_)
    simp only [bdryCopow_obj, ι_bdryCopow_map_assoc, colimit.ι_desc, Cofan.mk_pt,
      Cofan.mk_ι_app, colimit.ι_desc_assoc]
    exact c.descApp_comp _ _ _ _

@[reassoc (attr := simp)]
lemma BoundaryCone.ι_desc_app (c : BoundaryCone W n N) (Δ : SimplexCategoryᵒᵖ)
    (s : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s}) :
    Sigma.ι (fun _ : {s : Δ.unop ⟶ ⦋n⦌ // ¬ Epi s} ↦ N) s ≫ c.desc.app Δ =
      c.descApp s.1 s.2 := by
  simp

/-- If `f : N ⟶ Y _⦋n⦌` and `g : W ⟶ Y` are compatible with a boundary cone `c`, the two maps
`N ⊗ ∂Δ[n] ⟶ Y` agree. -/
lemma BoundaryCone.desc_comp_eq (c : BoundaryCone W n N) {Y : SimplicialObject C}
    (g : W ⟶ Y) (f : N ⟶ Y _⦋n⦌) (h : c.postcomp g = BoundaryCone.ofSimplex f) :
    c.desc ≫ g = bdryIncl N n ≫ copowStdDesc f := by
  ext Δ : 2
  refine Sigma.hom_ext _ _ (fun s ↦ ?_)
  simp only [NatTrans.comp_app, ι_desc_app_assoc, ι_bdryIncl_app_assoc, ι_copowStdDesc_app]
  rw [← BoundaryCone.descApp_ofSimplex, ← h, descApp_postcomp]

end Attach

section Pushout

variable [HasFiniteCoproducts C]

/-- Pushouts along a summand inclusion `∐_{a // p a} N ⟶ ∐_A N` exist: the pushout of
`f : ∐_{a // p a} N ⟶ Z` is `Z ⨿ ∐_{a // ¬ p a} N`. -/
lemma hasPushout_sigmaMap'_subtype {A : Type} [Finite A] (p : A → Prop) (N : C) {Z : C}
    (f : (∐ fun _ : {a // p a} ↦ N) ⟶ Z) :
    HasPushout f (Sigma.map' (f := fun _ : {a // p a} ↦ N) (g := fun _ : A ↦ N) Subtype.val
      (fun _ ↦ 𝟙 N)) := by
  classical
  let inr : (∐ fun _ : A ↦ N) ⟶ Z ⨿ ∐ fun _ : {a // ¬ p a} ↦ N := Sigma.desc fun a ↦
    if h : p a then Sigma.ι (fun _ : {a // p a} ↦ N) ⟨a, h⟩ ≫ f ≫ coprod.inl
    else Sigma.ι (fun _ : {a // ¬ p a} ↦ N) ⟨a, h⟩ ≫ coprod.inr
  have w : f ≫ coprod.inl = Sigma.map' (f := fun _ : {a // p a} ↦ N) (g := fun _ : A ↦ N)
      Subtype.val (fun _ ↦ 𝟙 N) ≫ inr := by
    refine Sigma.hom_ext _ _ (fun a ↦ ?_)
    simp [inr, a.2]
  refine ⟨⟨⟨PushoutCocone.mk _ _ w, PushoutCocone.IsColimit.mk _
    (fun s ↦ coprod.desc s.inl (Sigma.desc fun a ↦ Sigma.ι (fun _ : A ↦ N) a.1 ≫ s.inr))
    (fun s ↦ by simp) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩⟩
  · refine Sigma.hom_ext _ _ (fun a ↦ ?_)
    by_cases h : p a
    · have := Sigma.ι (fun _ : {a // p a} ↦ N) ⟨a, h⟩ ≫= s.condition
      simp only [Sigma.ι_comp_map'_assoc, Category.id_comp] at this
      simp [inr, h, this]
    · simp [inr, h]
  · refine coprod.hom_ext (by simpa using h₁) (Sigma.hom_ext _ _ (fun a ↦ ?_))
    have := Sigma.ι (fun _ : A ↦ N) a.1 ≫= h₂
    simp only [inr, colimit.ι_desc_assoc, Cofan.mk_pt, Cofan.mk_ι_app, a.2, dite_false,
      Category.assoc] at this
    simp [this]

/-- In a pushout square whose right leg `g` is an isomorphism, the left leg is one too. -/
lemma isIso_inl_of_isColimit {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {inl : X ⟶ Z}
    {inr : Y ⟶ Z} {w : f ≫ inl = g ≫ inr} (h : IsColimit (PushoutCocone.mk inl inr w))
    [IsIso g] : IsIso inl := by
  let d := PushoutCocone.IsColimit.desc h (𝟙 X) (inv g ≫ f) (by simp)
  have h₁ : inl ≫ d = 𝟙 X := PushoutCocone.IsColimit.inl_desc h _ _ _
  refine ⟨d, h₁, PushoutCocone.IsColimit.hom_ext h ?_ ?_⟩
  · change inl ≫ d ≫ inl = inl ≫ 𝟙 Z
    rw [reassoc_of% h₁, Category.comp_id]
  · have h₂ : inr ≫ d = inv g ≫ f := PushoutCocone.IsColimit.inr_desc h _ _ _
    change inr ≫ d ≫ inl = inr ≫ 𝟙 Z
    rw [reassoc_of% h₂, Category.comp_id, Category.assoc, w, IsIso.inv_hom_id_assoc]

variable {W : SimplicialObject C} {n : ℕ} {N : C} (c : BoundaryCone W n N)

instance (k : SimplexCategoryᵒᵖ) :
    HasColimit ((span c.desc (bdryIncl N n)).flip.obj k) := by
  have : HasPushout (c.desc.app k) ((bdryIncl N n).app k) :=
    hasPushout_sigmaMap'_subtype (fun s : k.unop ⟶ ⦋n⦌ ↦ ¬ Epi s) N _
  exact hasColimit_of_iso (diagramIsoSpan _)

namespace BoundaryCone

/-- The simplicial object obtained by attaching `N` to `W` along `c` as new nondegenerate
`n`-simplices: the pushout of `N ⊗ ∂Δ[n] ⟶ W` along `N ⊗ ∂Δ[n] ⟶ N ⊗ Δ[n]`. -/
def attach : SimplicialObject C := pushout c.desc (bdryIncl N n)

/-- The inclusion `W ⟶ c.attach`. -/
def attachInl : W ⟶ c.attach := pushout.inl _ _

/-- The map `N ⊗ Δ[n] ⟶ c.attach`. -/
def attachInr : stdCopow N n ⟶ c.attach := pushout.inr _ _

/-- The new nondegenerate `n`-simplices `N ⟶ c.attach _⦋n⦌`. -/
def attachι : N ⟶ c.attach _⦋n⦌ :=
  Sigma.ι (fun _ : ⦋n⦌ ⟶ ⦋n⦌ ↦ N) (𝟙 _) ≫ c.attachInr.app (op ⦋n⦌)

@[reassoc]
lemma attach_condition : c.desc ≫ c.attachInl = bdryIncl N n ≫ c.attachInr :=
  pushout.condition

@[reassoc]
lemma attach_condition_app (k : SimplexCategoryᵒᵖ) :
    c.desc.app k ≫ c.attachInl.app k = (bdryIncl N n).app k ≫ c.attachInr.app k :=
  NatTrans.congr_app c.attach_condition k

/-- In each degree, `c.attach` is a pushout. -/
def isColimitAttachApp (k : SimplexCategoryᵒᵖ) :
    IsColimit (PushoutCocone.mk _ _ (c.attach_condition_app k)) :=
  isColimitPushoutCoconeMapOfIsColimit ((evaluation _ _).obj k) _ (pushoutIsPushout _ _)

@[reassoc]
lemma ι_attachInr_app (k : SimplexCategoryᵒᵖ) (s : k.unop ⟶ ⦋n⦌) :
    Sigma.ι (fun _ : k.unop ⟶ ⦋n⦌ ↦ N) s ≫ c.attachInr.app k =
      c.attachι ≫ c.attach.map s.op := by
  rw [attachι, Category.assoc, ← c.attachInr.naturality, ι_stdCopow_map_assoc]
  simp

/-- The faces of the new simplices are given by the boundary cone. -/
lemma attachι_map {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n⦌) (hθ : ¬ Epi θ) :
    c.attachι ≫ c.attach.map θ.op = c.descApp θ hθ ≫ c.attachInl.app (op Δ) := by
  rw [← ι_attachInr_app]
  have := Sigma.ι (fun _ : {s : Δ ⟶ ⦋n⦌ // ¬ Epi s} ↦ N) ⟨θ, hθ⟩ ≫=
    c.attach_condition_app (op Δ)
  simp only [ι_desc_app_assoc, ι_bdryIncl_app_assoc] at this
  exact this.symm

lemma postcomp_attachInl_eq :
    c.postcomp c.attachInl = BoundaryCone.ofSimplex c.attachι := by
  refine ext' fun Δ hΔ θ ↦ ?_
  have hθ : ¬ Epi θ := fun h ↦ (lt_irrefl n)
    (lt_of_le_of_lt (SimplexCategory.len_le_of_epi θ) hΔ)
  rw [postcomp_π, ofSimplex_π, c.attachι_map θ hθ]
  rw [c.descApp_eq_π θ hθ hΔ]

/-- The attached object is universal: maps out of it are given by a map `g : W ⟶ Y` and an
`n`-simplex `f : N ⟶ Y _⦋n⦌` of `Y` whose faces are those prescribed by `c` and `g`. -/
def attachDesc {Y : SimplicialObject C} (g : W ⟶ Y) (f : N ⟶ Y _⦋n⦌)
    (h : c.postcomp g = BoundaryCone.ofSimplex f) : c.attach ⟶ Y :=
  pushout.desc g (copowStdDesc f) (c.desc_comp_eq g f h)

@[reassoc (attr := simp)]
lemma attachInl_attachDesc {Y : SimplicialObject C} (g : W ⟶ Y) (f : N ⟶ Y _⦋n⦌)
    (h : c.postcomp g = BoundaryCone.ofSimplex f) : c.attachInl ≫ c.attachDesc g f h = g :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma attachι_attachDesc_app {Y : SimplicialObject C} (g : W ⟶ Y) (f : N ⟶ Y _⦋n⦌)
    (h : c.postcomp g = BoundaryCone.ofSimplex f) :
    c.attachι ≫ (c.attachDesc g f h).app _ = f := by
  have := NatTrans.congr_app (pushout.inr_desc _ _ (c.desc_comp_eq g f h)) (op ⦋n⦌)
  rw [attachι, Category.assoc, attachInr, attachDesc, ← NatTrans.comp_app, this]
  simp

lemma attach_hom_ext {Y : SimplicialObject C} {a b : c.attach ⟶ Y}
    (h₁ : c.attachInl ≫ a = c.attachInl ≫ b) (h₂ : c.attachι ≫ a.app _ = c.attachι ≫ b.app _) :
    a = b := by
  refine pushout.hom_ext h₁ ?_
  ext k : 2
  refine Sigma.hom_ext _ _ (fun s ↦ ?_)
  change Sigma.ι (fun _ : k.unop ⟶ ⦋n⦌ ↦ N) s ≫ c.attachInr.app k ≫ a.app k =
    Sigma.ι (fun _ : k.unop ⟶ ⦋n⦌ ↦ N) s ≫ c.attachInr.app k ≫ b.app k
  rw [ι_attachInr_app_assoc, ι_attachInr_app_assoc, a.naturality, b.naturality,
    reassoc_of% h₂]

/-- In degrees `< n`, nothing new is attached. -/
lemma isIso_attachInl_app (k : SimplexCategoryᵒᵖ) (hk : k.unop.len < n) :
    IsIso (c.attachInl.app k) := by
  have : IsIso ((bdryIncl N n).app k) := by
    let e : {s : k.unop ⟶ ⦋n⦌ // ¬ Epi s} ≃ (k.unop ⟶ ⦋n⦌) :=
      Equiv.subtypeUnivEquiv (fun s h ↦ (lt_irrefl n)
        (lt_of_le_of_lt (SimplexCategory.len_le_of_epi s) hk))
    exact ⟨Sigma.map' e.symm (fun _ ↦ 𝟙 N), Sigma.hom_ext _ _ (fun s ↦ by simp [e]),
      Sigma.hom_ext _ _ (fun s ↦ by simp [e])⟩
  exact isIso_inl_of_isColimit (c.isColimitAttachApp k)

end BoundaryCone

end Pushout

end CategoryTheory.SimplicialObject
