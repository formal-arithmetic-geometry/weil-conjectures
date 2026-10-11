/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descending a representing object along a morphism

Let `p : X ⟶ Y` be a morphism in a category with pullbacks, let `F` be a presheaf on `Over Y` and
let `V` represent the restriction of `F` to `Over X`, so that `V` carries the canonical descent
datum `CategoryTheory.Functor.RepresentableBy.overDescentDatum`. If `J` is an object over `Y`
with `V ≅ J ×_Y X` through a morphism `q : V ⟶ J` which is invariant under the canonical
transport, and if both `F` and the functor of points of `J` satisfy the sheaf condition for the
base changes `T ×_Y X ⟶ T` of `p`, then `J` represents `F`
(`CategoryTheory.Functor.RepresentableBy.exists_representableBy_of_isPullback`).

The representation is compatible with the one of `V`: a point `a` of `V` over `f : T ⟶ X` and
its image `q ∘ a` in `J` correspond to the same element of `F`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Over

variable {C : Type u} [Category.{v} C] {X Y : C} (p : X ⟶ Y)

/-- The base change `T ×_Y X ⟶ T` of `p : X ⟶ Y` along an object `T` over `Y`, as a morphism in
`Over Y` whose source is the image under `Over.map p` of `T ×_Y X` over `X`. -/
noncomputable abbrev baseChangeπ [HasPullbacks C] (T : Over Y) :
    (Over.map p).obj (Over.mk (pullback.snd T.hom p)) ⟶ T :=
  Over.homMk (pullback.fst T.hom p) pullback.condition

end Over

namespace Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {X Y : C} {p : X ⟶ Y} {F : (Over Y)ᵒᵖ ⥤ Type w}
  {V : Over X} (r : ((Over.map p).op ⋙ F).RepresentableBy V)

/-- The identity of `Z.left`, viewed as a morphism from `Z` to `Over.mk (g ≫ p)` when
`Z.hom = g ≫ p`. -/
abbrev overHomMkIdOfEq {Z : Over Y} {g : Z.left ⟶ X} (h : g ≫ p = Z.hom) :
    Z ⟶ (Over.map p).obj (Over.mk g) :=
  Over.homMk (𝟙 Z.left) (by simp [h])

/-- The canonical transport only depends on the morphisms `f₁`, `f₂` and on the underlying
morphism of the point, not on how they are written. -/
lemma overTransport_left_congr {T : C} {f₁ f₂ f₁' f₂' : T ⟶ X} (h : f₁ ≫ p = f₂ ≫ p)
    (h' : f₁' ≫ p = f₂' ≫ p) (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') (a : Over.mk f₁ ⟶ V)
    (a' : Over.mk f₁' ⟶ V) (ha : a.left = a'.left) :
    (r.overTransport f₁ f₂ h a).left = (r.overTransport f₁' f₂' h' a').left := by
  subst e₁ e₂
  obtain rfl : a = a' := Over.OverMorphism.ext ha
  rfl

/-- The canonical transport along two equal morphisms is the identity. -/
lemma overTransport_left_of_eq {T : C} {f₁ f₂ : T ⟶ X} (h : f₁ ≫ p = f₂ ≫ p) (e : f₁ = f₂)
    (a : Over.mk f₁ ⟶ V) : (r.overTransport f₁ f₂ h a).left = a.left := by
  subst e
  rw [overTransport_self]

/-- Two points `a₁`, `a₂` of `V` over `g₁`, `g₂ : Z ⟶ X`, with `g₁ ≫ p = g₂ ≫ p = Z.hom`, whose
elements of `F(Z)` agree, are related by the canonical transport. -/
lemma eq_overTransport_of_map_eq {Z : Over Y} {g₁ g₂ : Z.left ⟶ X} (hg₁ : g₁ ≫ p = Z.hom)
    (hg₂ : g₂ ≫ p = Z.hom) (a₁ : Over.mk g₁ ⟶ V) (a₂ : Over.mk g₂ ⟶ V)
    (ha : F.map (overHomMkIdOfEq hg₁).op (r.homEquiv a₁) =
      F.map (overHomMkIdOfEq hg₂).op (r.homEquiv a₂)) :
    a₂ = r.overTransport g₁ g₂ (hg₁.trans hg₂.symm) a₁ := by
  let j : (Over.map p).obj (Over.mk g₂) ⟶ Z := Over.homMk (𝟙 Z.left) (by simp [hg₂])
  have h₁ : j ≫ overHomMkIdOfEq hg₁ = overMapHomMkId g₁ g₂ (hg₁.trans hg₂.symm) := by
    ext
    simp [j]
  have h₂ : j ≫ overHomMkIdOfEq hg₂ = 𝟙 _ := by
    ext
    simp [j]
  rw [overTransport, ← h₁, op_comp, Functor.map_comp_apply, ha, ← Functor.map_comp_apply,
    ← op_comp, h₂, op_id, Functor.map_id_apply]
  exact (r.homEquiv.symm_apply_apply a₂).symm

lemma overHomMkIdOfEq_comp_map_homMk {W : Over X} {Z : Over Y}
    (i : Z ⟶ (Over.map p).obj W) :
    overHomMkIdOfEq (g := i.left ≫ W.hom) (by rw [Category.assoc]; exact Over.w i) ≫
      (Over.map p).map (Over.homMk i.left : Over.mk (i.left ≫ W.hom) ⟶ W) = i := by
  ext
  simp

/-- If two morphisms `p₁ p₂ : Z ⟶ (Over.map p).obj W` pull the element of a point `b` of `V`
over `W` back to the same element, then the two restrictions of `b` are related by the canonical
transport. -/
lemma overTransport_homMk_comp_of_map_eq {W : Over X} (b : W ⟶ V) {Z : Over Y}
    (p₁ p₂ : Z ⟶ (Over.map p).obj W)
    (hx : F.map p₁.op (r.homEquiv b) = F.map p₂.op (r.homEquiv b)) :
    r.overTransport (p₁.left ≫ W.hom) (p₂.left ≫ W.hom)
        (by rw [Category.assoc, Category.assoc]; exact (Over.w p₁).trans (Over.w p₂).symm)
        ((Over.homMk p₁.left : Over.mk (p₁.left ≫ W.hom) ⟶ W) ≫ b) =
      (Over.homMk p₂.left : Over.mk (p₂.left ≫ W.hom) ⟶ W) ≫ b := by
  refine (r.eq_overTransport_of_map_eq (by rw [Category.assoc]; exact Over.w p₁)
    (by rw [Category.assoc]; exact Over.w p₂) _ _ ?_).symm
  rw [r.homEquiv_comp, r.homEquiv_comp]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  erw [← Functor.map_comp_apply F, ← Functor.map_comp_apply F]
  simp only [← op_comp,
    overHomMkIdOfEq_comp_map_homMk]
  exact hx

/-- Conversely to `eq_overTransport_of_map_eq`, a point and its canonical transport have the same
element of `F(Z)`. -/
lemma map_overHomMkIdOfEq_overTransport {Z : Over Y} {g₁ g₂ : Z.left ⟶ X}
    (hg₁ : g₁ ≫ p = Z.hom) (hg₂ : g₂ ≫ p = Z.hom) (a₁ : Over.mk g₁ ⟶ V) :
    F.map (overHomMkIdOfEq hg₂).op
        (r.homEquiv (r.overTransport g₁ g₂ (hg₁.trans hg₂.symm) a₁)) =
      F.map (overHomMkIdOfEq hg₁).op (r.homEquiv a₁) := by
  erw [homEquiv_overTransport]
  erw [← Functor.map_comp_apply F]
  have e : overHomMkIdOfEq hg₂ ≫ overMapHomMkId g₁ g₂ (hg₁.trans hg₂.symm) =
      overHomMkIdOfEq hg₁ := by
    ext
    simp
  rw [← op_comp, e]

section Descent

variable {J : Over Y} {q : V.left ⟶ J.left}

/-- A point of `J` over `T` lifts to a point of `V ≅ J ×_Y X` over `T ×_Y X`. -/
noncomputable def liftPoint [HasPullbacks C] (hq : IsPullback q V.hom J.hom p)
    (T : Over Y) (b : T ⟶ J) :
    Over.mk (pullback.snd T.hom p) ⟶ V :=
  Over.homMk (hq.lift (pullback.fst T.hom p ≫ b.left) (pullback.snd T.hom p)
    (by rw [Category.assoc, Over.w b, pullback.condition])) (by simp)

@[reassoc (attr := simp)]
lemma liftPoint_left_comp [HasPullbacks C] (hq : IsPullback q V.hom J.hom p)
    (T : Over Y) (b : T ⟶ J) :
    (liftPoint hq T b).left ≫ q = pullback.fst T.hom p ≫ b.left :=
  hq.lift_fst _ _ _


/-- Two points of `V` over the same morphism with the same image in `J` are equal. -/
lemma hom_ext_of_isPullback (hq : IsPullback q V.hom J.hom p) {T : C} {f : T ⟶ X}
    {a a' : Over.mk f ⟶ V} (h : a.left ≫ q = a'.left ≫ q) : a = a' := by
  ext
  exact hq.hom_ext h (by rw [Over.w a, Over.w a'])

variable [HasPullbacks C]

/-- The invariance of `q` under the canonical transport of `r`. -/
def IsTransportInvariant (q : V.left ⟶ J.left) : Prop :=
  ∀ {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
    (r.overTransport f₁ f₂ h a).left ≫ q = a.left ≫ q

/-- The image `q ∘ a` in `J` of the point `a` of `V` corresponding to the restriction of a section
`s ∈ F(T)` to `T ×_Y X`. -/
noncomputable def descendSection (q : V.left ⟶ J.left) (hq : IsPullback q V.hom J.hom p)
    (T : Over Y) (s : F.obj (op T)) :
    (Over.map p).obj (Over.mk (pullback.snd T.hom p)) ⟶ J :=
  Over.homMk ((r.homEquiv.symm (F.map (Over.baseChangeπ p T).op s)).left ≫ q) (by
    simp only [Over.map_obj_hom, Over.mk_hom, Category.assoc, hq.w]
    rw [← Category.assoc, Over.w (r.homEquiv.symm (F.map (Over.baseChangeπ p T).op s))])

variable {r}

lemma compatible_homEquiv_liftPoint (hq : IsPullback q V.hom J.hom p)
    (hinv : r.IsTransportInvariant q) (T : Over Y) (b : T ⟶ J) {Z : Over Y}
    (p₁ p₂ : Z ⟶ (Over.map p).obj (Over.mk (pullback.snd T.hom p)))
    (h : p₁ ≫ Over.baseChangeπ p T = p₂ ≫ Over.baseChangeπ p T) :
    F.map p₁.op (r.homEquiv (liftPoint hq T b)) = F.map p₂.op (r.homEquiv (liftPoint hq T b)) := by
  have hl : p₁.left ≫ pullback.fst T.hom p = p₂.left ≫ pullback.fst T.hom p :=
    congrArg CommaMorphism.left h
  let W : Over X := Over.mk (pullback.snd T.hom p)
  let a (i : Z ⟶ (Over.map p).obj W) : Over.mk (i.left ≫ W.hom) ⟶ V :=
    (Over.homMk i.left : Over.mk (i.left ≫ W.hom) ⟶ W) ≫ liftPoint hq T b
  have hw (i : Z ⟶ (Over.map p).obj W) : (i.left ≫ W.hom) ≫ p = Z.hom := by
    rw [Category.assoc]
    exact Over.w i
  have hF (i : Z ⟶ (Over.map p).obj W) :
      F.map i.op (r.homEquiv (liftPoint hq T b)) =
        F.map (overHomMkIdOfEq (hw i)).op (r.homEquiv (a i)) := by
    rw [r.homEquiv_comp]
    erw [← Functor.map_comp_apply F]
    exact congrArg (fun φ ↦ F.map φ.op _) (overHomMkIdOfEq_comp_map_homMk i).symm
  have ha : a p₂ = r.overTransport _ _ ((hw p₁).trans (hw p₂).symm) (a p₁) :=
    hom_ext_of_isPullback hq (by
      rw [hinv]
      simp [a, W, reassoc_of% hl])
  rw [hF, hF, ha, map_overHomMkIdOfEq_overTransport]

lemma compatible_descendSection (hq : IsPullback q V.hom J.hom p)
    (hinv : r.IsTransportInvariant q) (T : Over Y) (s : F.obj (op T)) {Z : Over Y}
    (p₁ p₂ : Z ⟶ (Over.map p).obj (Over.mk (pullback.snd T.hom p)))
    (h : p₁ ≫ Over.baseChangeπ p T = p₂ ≫ Over.baseChangeπ p T) :
    p₁ ≫ r.descendSection q hq T s = p₂ ≫ r.descendSection q hq T s := by
  let a := r.homEquiv.symm (F.map (Over.baseChangeπ p T).op s)
  have hx : F.map p₁.op (r.homEquiv a) = F.map p₂.op (r.homEquiv a) := by
    simp only [a, Equiv.apply_symm_apply]
    erw [← Functor.map_comp_apply F, ← Functor.map_comp_apply F]
    rw [← op_comp, ← op_comp, h]
  have ht := r.overTransport_homMk_comp_of_map_eq a p₁ p₂ hx
  have := congrArg (fun c ↦ c.left ≫ q) ht
  rw [hinv] at this
  ext
  simpa [descendSection, a] using this

/-- **A representing object descends.** Let `p : X ⟶ Y`, let `F` be a presheaf on `Over Y` and let
`r` exhibit `V` as a representing object of the restriction of `F` to `Over X`. Let `J` be an
object over `Y` and `q : V ⟶ J` exhibit `V` as `J ×_Y X`, invariant under the canonical
transport of `r`. If `F` and the functor of points of `J` satisfy the sheaf condition for every
base change `T ×_Y X ⟶ T` of `p`, then `J` represents `F`, compatibly with `r`: a point `a` of
`V` over `f : T ⟶ X` and its image `q ∘ a` in `J` correspond to the same element of `F`. -/
theorem exists_representableBy_of_isPullback (hq : IsPullback q V.hom J.hom p)
    (hinv : r.IsTransportInvariant q)
    (hF : ∀ T : Over Y, Presieve.IsSheafFor F (.singleton (Over.baseChangeπ p T)))
    (hJ : ∀ T : Over Y, Presieve.IsSheafFor (yoneda.obj J) (.singleton (Over.baseChangeπ p T))) :
    ∃ e : F.RepresentableBy J, ∀ {T : C} (f : T ⟶ X) (a : Over.mk f ⟶ V),
      e.homEquiv (Over.homMk (a.left ≫ q) (by
          rw [Category.assoc, hq.w, ← Category.assoc, Over.w a]; rfl) :
        Over.mk (f ≫ p) ⟶ J) = r.homEquiv a := by
  have hψ (T : Over Y) (b : T ⟶ J) := Presieve.isSheafFor_singleton.1 (hF T)
    (r.homEquiv (liftPoint hq T b)) (compatible_homEquiv_liftPoint hq hinv T b)
  have hφ (T : Over Y) (s : F.obj (op T)) := Presieve.isSheafFor_singleton.1 (hJ T)
    (r.descendSection q hq T s) (compatible_descendSection hq hinv T s)
  let ψ (T : Over Y) (b : T ⟶ J) : F.obj (op T) := (hψ T b).exists.choose
  let φ (T : Over Y) (s : F.obj (op T)) : T ⟶ J := (hφ T s).exists.choose
  have hψs (T : Over Y) (b : T ⟶ J) :
      F.map (Over.baseChangeπ p T).op (ψ T b) = r.homEquiv (liftPoint hq T b) :=
    (hψ T b).exists.choose_spec
  have hφs (T : Over Y) (s : F.obj (op T)) :
      Over.baseChangeπ p T ≫ φ T s = r.descendSection q hq T s :=
    (hφ T s).exists.choose_spec
  have hψu (T : Over Y) (b : T ⟶ J) (y : F.obj (op T))
      (hy : F.map (Over.baseChangeπ p T).op y = r.homEquiv (liftPoint hq T b)) : y = ψ T b :=
    (hψ T b).unique hy (hψs T b)
  have hφu (T : Over Y) (s : F.obj (op T)) (g : T ⟶ J)
      (hg : Over.baseChangeπ p T ≫ g = r.descendSection q hq T s) : g = φ T s :=
    (hφ T s).unique hg (hφs T s)
  -- the two constructions are inverse to each other
  have hlift (T : Over Y) (s : F.obj (op T)) :
      liftPoint hq T (φ T s) = r.homEquiv.symm (F.map (Over.baseChangeπ p T).op s) :=
    hom_ext_of_isPullback hq (by
      rw [liftPoint_left_comp]
      exact congrArg CommaMorphism.left (hφs T s))
  have hφψ (T : Over Y) (b : T ⟶ J) : φ T (ψ T b) = b := by
    refine (hφu T _ b ?_).symm
    ext
    simp only [descendSection, Over.comp_left, Over.homMk_left]
    erw [hψs, Equiv.symm_apply_apply, liftPoint_left_comp]
  have hψφ (T : Over Y) (s : F.obj (op T)) : ψ T (φ T s) = s :=
    (hψu T _ s (by rw [hlift]; exact (r.homEquiv.apply_symm_apply _).symm)).symm
  refine ⟨{ homEquiv := fun {T} ↦ ⟨ψ T, φ T, hφψ T, hψφ T⟩
            homEquiv_comp := fun {T₁ T₂} g b ↦ ?_ }, fun {T} f a ↦ ?_⟩
  · -- naturality
    let h : Over.mk (pullback.snd T₁.hom p) ⟶ Over.mk (pullback.snd T₂.hom p) :=
      Over.homMk (pullback.map _ _ _ _ g.left (𝟙 X) (𝟙 Y) (by simp) (by simp)) (by simp)
    have e : Over.baseChangeπ p T₁ ≫ g = (Over.map p).map h ≫ Over.baseChangeπ p T₂ := by
      ext
      simp [h]
    have e' : h ≫ liftPoint hq T₂ b = liftPoint hq T₁ (g ≫ b) :=
      hom_ext_of_isPullback hq (by simp [h])
    refine (hψu T₁ _ _ ?_).symm
    erw [← Functor.map_comp_apply F]
    rw [← op_comp, e, op_comp]
    erw [Functor.map_comp_apply F]
    erw [hψs]
    rw [← e']
    exact (r.homEquiv_comp h _).symm
  · -- compatibility with `r`
    let T₀ : Over Y := Over.mk (f ≫ p)
    have hg₁ : (pullback.fst T₀.hom p ≫ f) ≫ p = pullback.snd T₀.hom p ≫ p := by
      rw [Category.assoc]
      exact pullback.condition
    let a₁ : Over.mk (pullback.fst T₀.hom p ≫ f) ⟶ V :=
      (Over.homMk (pullback.fst T₀.hom p) : Over.mk (pullback.fst T₀.hom p ≫ f) ⟶ Over.mk f) ≫ a
    have hπ : Over.baseChangeπ p T₀ = overHomMkIdOfEq (Z := (Over.map p).obj
        (Over.mk (pullback.snd T₀.hom p))) hg₁ ≫ (Over.map p).map
          (Over.homMk (pullback.fst T₀.hom p) :
            Over.mk (pullback.fst T₀.hom p ≫ f) ⟶ Over.mk f) := by
      ext
      simp
    have hid : overHomMkIdOfEq (Z := (Over.map p).obj (Over.mk (pullback.snd T₀.hom p)))
        (g := pullback.snd T₀.hom p) rfl = 𝟙 _ := by
      ext
      simp
    have ht : liftPoint hq T₀ (Over.homMk (a.left ≫ q) (by
          rw [Category.assoc, hq.w, ← Category.assoc, Over.w a]; rfl) : Over.mk (f ≫ p) ⟶ J) =
        r.overTransport _ _ (hg₁.trans rfl) a₁ :=
      hom_ext_of_isPullback hq (by
        rw [hinv, liftPoint_left_comp]
        simp [a₁])
    refine (hψu T₀ _ _ ?_).symm
    have hm := r.map_overHomMkIdOfEq_overTransport
      (Z := (Over.map p).obj (Over.mk (pullback.snd T₀.hom p)))
      (g₁ := pullback.fst T₀.hom p ≫ f) (g₂ := pullback.snd T₀.hom p) hg₁ rfl a₁
    rw [hid, op_id, Functor.map_id_apply, ← ht] at hm
    erw [hm, r.homEquiv_comp]
    rw [hπ, op_comp]
    erw [Functor.map_comp_apply F]
    rfl

end Descent

end Functor.RepresentableBy

end CategoryTheory
