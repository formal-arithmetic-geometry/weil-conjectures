/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Sheaves on the small étale site represented by finite étale schemes: the affine case

Let `F` be a sheaf of sets on the small étale site of a scheme `Y`, let `p : W ⟶ B` be a
surjective morphism of étale `Y`-schemes with `W` and `B` affine, and suppose that the
restriction of `F` to étale `W`-schemes is represented by a finite étale `W`-scheme `V`. Then the
restriction of `F` to étale `B`-schemes is represented by a finite étale `B`-scheme
(`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isAffine`).

This is effective étale descent for finite étale schemes along `W ⟶ B`: the representation of
`F` over `W` gives `V` a descent datum, the coaction `γ : V ×_B W ⟶ V` transporting a point of
`V` over `w₁` to the point over `w₂` representing the same section of `F`. By affine descent
(`AlgebraicGeometry.exists_isPullback_of_coaction`) `V = X ×_B W` for an affine `B`-scheme `X`,
finite étale by fpqc descent, and `X` represents `F` over `B` because étale surjections are
effective epimorphisms and `F` is a sheaf.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.overElt`: the section of `F` attached to a morphism
  into a representing object over a base, and its basic properties.
- `AlgebraicGeometry.Scheme.Etale.existsUnique_of_isSheaf`: the sheaf condition for a jointly
  surjective family of étale morphisms.
- `AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isAffine`: the affine descent step.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type*} [Category* C] {G : Cᵒᵖ ⥤ Type w} {B : C} {V : Over B}
  (r : ((Over.forget B).op ⋙ G).RepresentableBy V)

/-- The section of `G` over `T` corresponding to a morphism `a : T ⟶ V.left`, where `V`
represents the restriction of `G` to objects over `B` and `T` is viewed over `B` through `a`. -/
def overElt {T : C} (a : T ⟶ V.left) : G.obj (op T) :=
  r.homEquiv (Over.homMk a : Over.mk (a ≫ V.hom) ⟶ V)

lemma overElt_comp {T T' : C} (h : T' ⟶ T) (a : T ⟶ V.left) :
    r.overElt (h ≫ a) = G.map h.op (r.overElt a) := by
  have e : (Over.homMk (h ≫ a) : Over.mk ((h ≫ a) ≫ V.hom) ⟶ V) =
      (Over.homMk h (by simp) : Over.mk ((h ≫ a) ≫ V.hom) ⟶ Over.mk (a ≫ V.hom)) ≫
        Over.homMk a := by
    ext
    simp
  rw [overElt, e, r.homEquiv_comp]
  rfl

lemma overElt_left {Z : Over B} (φ : Z ⟶ V) : r.overElt φ.left = r.homEquiv φ := by
  have e : (Over.homMk φ.left : Over.mk (φ.left ≫ V.hom) ⟶ V) =
      (Over.homMk (𝟙 Z.left) (by simp) : Over.mk (φ.left ≫ V.hom) ⟶ Z) ≫ φ := by
    ext
    simp
  rw [overElt, e, r.homEquiv_comp]
  change G.map (𝟙 Z.left).op _ = _
  simp

lemma overElt_injective {T : C} {a a' : T ⟶ V.left} (h : a ≫ V.hom = a' ≫ V.hom)
    (h' : r.overElt a = r.overElt a') : a = a' := by
  have := r.homEquiv.injective
    (show r.homEquiv (Over.homMk a h : Over.mk (a' ≫ V.hom) ⟶ V) =
      r.homEquiv (Over.homMk a' : Over.mk (a' ≫ V.hom) ⟶ V) by
      rw [← overElt_left, ← overElt_left]
      exact h')
  exact congr_arg CommaMorphism.left this

lemma exists_overElt_eq {T : C} (g : T ⟶ B) (s : G.obj (op T)) :
    ∃ a : T ⟶ V.left, a ≫ V.hom = g ∧ r.overElt a = s :=
  ⟨(r.homEquiv.symm s : Over.mk g ⟶ V).left, Over.w _, by
    rw [overElt_left]; exact (r.homEquiv (X := Over.mk g)).apply_symm_apply s⟩

end CategoryTheory.Functor.RepresentableBy

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

namespace Etale

@[simp, reassoc]
lemma comp_left {U V W : Y.Etale} (f : U ⟶ V) (g : V ⟶ W) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

@[simp]
lemma id_left (U : Y.Etale) : (𝟙 U : U ⟶ U).left = 𝟙 U.left :=
  rfl

/-- A morphism of étale `Y`-schemes from a morphism of schemes over `Y`. -/
noncomputable def homMk {U V : Y.Etale} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom) : U ⟶ V :=
  MorphismProperty.Over.homMk f w

@[simp]
lemma homMk_left {U V : Y.Etale} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom) :
    (homMk f w).left = f :=
  rfl


section AffineDescent

variable (F : Sheaf Y.smallEtaleTopology (Type w)) {B W : Y.Etale} (p : W ⟶ B) {V : Over W}
  (r : ((Over.forget W).op ⋙ F.obj).RepresentableBy V)

lemma over_w (V : Over W) : V.hom.left ≫ W.hom = V.left.hom :=
  MorphismProperty.Over.w V.hom

lemma w_left {U U' : Y.Etale} (f : U ⟶ U') : f.left ≫ U'.hom = U.hom :=
  MorphismProperty.Over.w f

/-- `V ×_B W` as an étale `Y`-scheme. -/
noncomputable abbrev PC : Y.Etale := Etale.mk (pullback.snd (V.hom.left ≫ p.left) p.left ≫ W.hom)

/-- The first projection `V ×_B W ⟶ V`. -/
noncomputable def pr₁C : PC p (V := V) ⟶ V.left :=
  homMk (pullback.fst (V.hom.left ≫ p.left) p.left) (by
    change _ = pullback.snd (V.hom.left ≫ p.left) p.left ≫ W.hom
    have := pullback.condition_assoc (f := V.hom.left ≫ p.left) (g := p.left) B.hom
    simp only [Category.assoc, w_left] at this
    exact this)

/-- The second projection `V ×_B W ⟶ W`. -/
noncomputable def pr₂C : PC p (V := V) ⟶ W :=
  homMk (pullback.snd (V.hom.left ≫ p.left) p.left) rfl

@[simp] lemma pr₁C_left : (pr₁C p (V := V)).left = pullback.fst (V.hom.left ≫ p.left) p.left := rfl
@[simp] lemma pr₂C_left : (pr₂C p (V := V)).left = pullback.snd (V.hom.left ≫ p.left) p.left := rfl

/-- The coaction `γ : V ×_B W ⟶ V`: it sends a point `(x, w)` to the point of `V` over `w`
representing the same section of `F` as `x`. -/
noncomputable def γC : PC p (V := V) ⟶ V.left :=
  (r.exists_overElt_eq (pr₂C p) (r.overElt (pr₁C p))).choose

lemma γC_hom : γC F p r ≫ V.hom = pr₂C p :=
  (r.exists_overElt_eq (pr₂C p) (r.overElt (pr₁C p))).choose_spec.1

lemma overElt_γC : r.overElt (γC F p r) = r.overElt (pr₁C p) :=
  (r.exists_overElt_eq (pr₂C p) (r.overElt (pr₁C p))).choose_spec.2

lemma γ_v : (γC F p r).left ≫ V.hom.left = pullback.snd (V.hom.left ≫ p.left) p.left :=
  congr_arg (fun f ↦ f.left) (γC_hom F p r)

/-- The coaction is counital. -/
lemma d_γ : coactionUnit p.left V.hom.left ≫ (γC F p r).left = 𝟙 _ := by
  let dC : V.left ⟶ PC p (V := V) :=
    homMk (coactionUnit p.left V.hom.left) (by
      change _ ≫ pullback.snd _ _ ≫ W.hom = _
      rw [pullback.lift_snd_assoc, over_w])
  have h₁ : dC ≫ pr₁C p = 𝟙 _ := hom_ext (by simp [dC])
  have h₂ : dC ≫ pr₂C p = V.hom := hom_ext (by simp [dC])
  have : dC ≫ γC F p r = 𝟙 _ := by
    refine r.overElt_injective (by rw [Category.assoc, γC_hom, h₂, Category.id_comp]) ?_
    rw [r.overElt_comp, overElt_γC, ← r.overElt_comp, h₁]
  exact congr_arg (fun f ↦ f.left) this

/-- The coaction is coassociative. -/
lemma γ₁_γ : coactionMap p.left V.hom.left (γC F p r).left (γ_v F p r) ≫ (γC F p r).left =
    coactionForget p.left V.hom.left ≫ (γC F p r).left := by
  let P₂C : Y.Etale := Etale.mk
    (pullback.snd (pullback.snd (V.hom.left ≫ p.left) p.left ≫ p.left) p.left ≫ W.hom)
  let fstC : P₂C ⟶ PC p (V := V) := homMk (pullback.fst _ _) (by
    change _ ≫ pullback.snd _ _ ≫ W.hom = pullback.snd _ _ ≫ W.hom
    have := pullback.condition_assoc (f := pullback.snd (V.hom.left ≫ p.left) p.left ≫ p.left)
      (g := p.left) B.hom
    simp only [Category.assoc, w_left] at this
    exact this)
  let γ₁C : P₂C ⟶ PC p (V := V) := homMk
    (coactionMap p.left V.hom.left (γC F p r).left (γ_v F p r)) (by
      change _ ≫ pullback.snd _ _ ≫ W.hom = pullback.snd _ _ ≫ W.hom
      simp)
  let π₁C : P₂C ⟶ PC p (V := V) := homMk
    (coactionForget p.left V.hom.left) (by
      change _ ≫ pullback.snd _ _ ≫ W.hom = pullback.snd _ _ ≫ W.hom
      simp)
  have e₁ : γ₁C ≫ pr₁C p = fstC ≫ γC F p r := hom_ext (by simp [γ₁C, fstC])
  have e₂ : γ₁C ≫ pr₂C p = π₁C ≫ pr₂C p := hom_ext (by simp [γ₁C, π₁C])
  have e₃ : π₁C ≫ pr₁C p = fstC ≫ pr₁C p := hom_ext (by simp [π₁C, fstC])
  have : γ₁C ≫ γC F p r = π₁C ≫ γC F p r := by
    refine r.overElt_injective (by simp only [Category.assoc, γC_hom, e₂]) ?_
    rw [r.overElt_comp, r.overElt_comp, overElt_γC, ← r.overElt_comp, ← r.overElt_comp, e₁, e₃,
      r.overElt_comp, overElt_γC, ← r.overElt_comp]
  exact congr_arg (fun f ↦ f.left) this

variable {F p r}

variable {N : Scheme.{u}} {n : N ⟶ B.left} {q : V.left.left ⟶ N}
  (hpb : IsPullback q V.hom.left n p.left)
  (hq : (γC F p r).left ≫ q = pullback.fst (V.hom.left ≫ p.left) p.left ≫ q)

include hq in
/-- Two points of `V` over the same point of `B` representing the same section of `F` have the
same image in the descended scheme. -/
lemma left_comp_q_eq {T : Y.Etale} {a₁ a₂ : T ⟶ V.left}
    (hp : a₁ ≫ V.hom ≫ p = a₂ ≫ V.hom ≫ p) (h : r.overElt a₁ = r.overElt a₂) :
    a₁.left ≫ q = a₂.left ≫ q := by
  have hc : a₁.left ≫ V.hom.left ≫ p.left = (a₂ ≫ V.hom).left ≫ p.left :=
    by simpa using congr_arg (fun f ↦ f.left) hp
  let θ : T ⟶ PC p (V := V) := homMk (pullback.lift _ _ hc) (by
    change _ ≫ pullback.snd _ _ ≫ W.hom = _
    rw [pullback.lift_snd_assoc, w_left])
  have h₁ : θ ≫ pr₁C p = a₁ := hom_ext (by simp [θ])
  have h₂ : θ ≫ pr₂C p = a₂ ≫ V.hom := hom_ext (by simp [θ])
  have : θ ≫ γC F p r = a₂ := by
    refine r.overElt_injective (by rw [Category.assoc, γC_hom, h₂]) ?_
    rw [r.overElt_comp, overElt_γC, ← r.overElt_comp, h₁, h]
  rw [← this, comp_left, Category.assoc, hq, ← Category.assoc, ← pr₁C_left, ← comp_left, h₁]


section Representation

variable (p) in
/-- For `Z` over `B`, the étale `Y`-scheme `Z ×_B W`. -/
noncomputable abbrev ZW (Z : Over B) : Y.Etale :=
  Etale.mk (pullback.fst Z.hom.left p.left ≫ Z.left.hom)

variable (p) in
/-- The projection `Z ×_B W ⟶ Z`. -/
noncomputable def prZ (Z : Over B) : ZW p Z ⟶ Z.left :=
  homMk (pullback.fst Z.hom.left p.left) rfl

variable (p) in
/-- The projection `Z ×_B W ⟶ W`. -/
noncomputable def prW (Z : Over B) : ZW p Z ⟶ W :=
  homMk (pullback.snd Z.hom.left p.left) (by
    change _ = pullback.fst Z.hom.left p.left ≫ Z.left.hom
    rw [← w_left p, ← w_left Z.hom]
    exact (pullback.condition_assoc _).symm)

@[simp] lemma prZ_left (Z : Over B) : (prZ p Z).left = pullback.fst Z.hom.left p.left := rfl
@[simp] lemma prW_left (Z : Over B) : (prW p Z).left = pullback.snd Z.hom.left p.left := rfl

lemma prW_comp (Z : Over B) : prW p Z ≫ p = prZ p Z ≫ Z.hom :=
  hom_ext (by simp [pullback.condition])

instance (Z : Over B) [Surjective p.left] : Surjective (prZ p Z).left := by
  rw [prZ_left]
  infer_instance

-- `hpb` is kept as an argument so that `descLeft` and its API take it uniformly
set_option linter.unusedSectionVars false in
include hpb hq in
lemma exists_fst_comp_eq [Surjective p.left] (Z : Over B) (s : F.obj.obj (op Z.left)) :
    ∃ m : Z.left.left ⟶ N, ∀ a : ZW p Z ⟶ V.left, a ≫ V.hom = prW p Z →
      r.overElt a = F.obj.map (prZ p Z).op s → pullback.fst Z.hom.left p.left ≫ m = a.left ≫ q := by
  obtain ⟨a, ha₁, ha₂⟩ := r.exists_overElt_eq (prW p Z) (F.obj.map (prZ p Z).op s)
  -- the kernel pair of `Z ×_B W ⟶ Z`
  let K : Y.Etale := Etale.mk (pullback.fst (pullback.fst Z.hom.left p.left)
    (pullback.fst Z.hom.left p.left) ≫ (ZW p Z).hom)
  let k₁ : K ⟶ ZW p Z := homMk (pullback.fst _ _) rfl
  let k₂ : K ⟶ ZW p Z := homMk (pullback.snd _ _) (by
    change pullback.snd _ _ ≫ pullback.fst _ _ ≫ Z.left.hom =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ Z.left.hom
    rw [← pullback.condition_assoc])
  have hk : k₁ ≫ prZ p Z = k₂ ≫ prZ p Z := hom_ext (by simp [k₁, k₂, pullback.condition])
  have hK : k₁.left ≫ a.left ≫ q = k₂.left ≫ a.left ≫ q := by
    have := left_comp_q_eq hq (a₁ := k₁ ≫ a) (a₂ := k₂ ≫ a)
      (by simp only [Category.assoc, reassoc_of% ha₁, prW_comp, reassoc_of% hk])
      (by rw [r.overElt_comp, r.overElt_comp, ha₂, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← op_comp, ← op_comp, hk])
    simpa using this
  refine ⟨EffectiveEpi.desc (pullback.fst Z.hom.left p.left) (a.left ≫ q) fun g₁ g₂ hg ↦ ?_,
    fun a' ha'₁ ha'₂ ↦ ?_⟩
  · calc g₁ ≫ a.left ≫ q = pullback.lift g₁ g₂ hg ≫ k₁.left ≫ a.left ≫ q := by simp [k₁]
      _ = pullback.lift g₁ g₂ hg ≫ k₂.left ≫ a.left ≫ q := by rw [hK]
      _ = g₂ ≫ a.left ≫ q := by simp [k₂]
  · have : a' = a := r.overElt_injective (ha'₁.trans ha₁.symm) (ha'₂.trans ha₂.symm)
    rw [this, EffectiveEpi.fac]

/-- The morphism `Z ⟶ X` attached to a section of `F` over `Z`, by descent along
`Z ×_B W ⟶ Z`. -/
noncomputable def descLeft [Surjective p.left] (Z : Over B) (s : F.obj.obj (op Z.left)) :
    Z.left.left ⟶ N :=
  (exists_fst_comp_eq hpb hq Z s).choose

lemma fst_descLeft [Surjective p.left] (Z : Over B) (s : F.obj.obj (op Z.left))
    (a : ZW p Z ⟶ V.left) (ha₁ : a ≫ V.hom = prW p Z)
    (ha₂ : r.overElt a = F.obj.map (prZ p Z).op s) :
    pullback.fst Z.hom.left p.left ≫ descLeft hpb hq Z s = a.left ≫ q :=
  (exists_fst_comp_eq hpb hq Z s).choose_spec a ha₁ ha₂

lemma descLeft_comp [Surjective p.left] (Z : Over B) (s : F.obj.obj (op Z.left)) :
    descLeft hpb hq Z s ≫ n = Z.hom.left := by
  obtain ⟨a, ha₁, ha₂⟩ := r.exists_overElt_eq (prW p Z) (F.obj.map (prZ p Z).op s)
  rw [← cancel_epi (pullback.fst Z.hom.left p.left), reassoc_of% fst_descLeft hpb hq Z s a ha₁ ha₂,
    hpb.w, ← Category.assoc, ← comp_left, ha₁, prW_left, pullback.condition]

variable (n) in
/-- The descended scheme, as an étale `Y`-scheme. -/
noncomputable abbrev XC [AlgebraicGeometry.Etale n] : Y.Etale := Etale.mk (n ≫ B.hom)

variable (n) in
/-- The descended scheme, as an object over `B`. -/
noncomputable def XO [AlgebraicGeometry.Etale n] : Over B := Over.mk (homMk n rfl : XC n ⟶ B)

@[simp] lemma XO_left [AlgebraicGeometry.Etale n] : (XO n).left = XC n := rfl
@[simp] lemma XO_hom_left [AlgebraicGeometry.Etale n] : (XO n).hom.left = n := rfl

/-- The morphism `Z ⟶ X` over `B` attached to a section of `F` over `Z`. -/
noncomputable def desc [Surjective p.left] [AlgebraicGeometry.Etale n] (Z : Over B)
    (s : F.obj.obj (op Z.left)) : Z ⟶ XO n :=
  Over.homMk (homMk (descLeft hpb hq Z s) (by
    change _ ≫ n ≫ B.hom = _
    rw [reassoc_of% descLeft_comp, w_left])) (hom_ext (by simp [descLeft_comp]))

@[simp] lemma desc_left_left [Surjective p.left] [AlgebraicGeometry.Etale n] (Z : Over B)
    (s : F.obj.obj (op Z.left)) : (desc hpb hq Z s).left.left = descLeft hpb hq Z s := rfl


end Representation

end AffineDescent


end Etale

end AlgebraicGeometry.Scheme
