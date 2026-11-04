/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Descent data from natural bijections on the localized pro-étale site

Let `p : V ⟶ X` be weakly étale, let `E` be a scheme weakly étale over `V`, and let `A` be a
presheaf on the small pro-étale site of `X`. Suppose that for every object `W` of the localized
site over `V` we are given a bijection `rho W` between the morphisms over `V` from `W` to `E` and
the sections `A(W)`, natural in `W`. Then `E` carries a descent datum relative to `p`, whose
transport preserves `rho`: a point of `E` over `a : W ⟶ V` and its transport over `b : W ⟶ V`
have the same `rho`-section of `A(W)`.

The descent datum is determined by its value `φ : E ×_X V ⟶ E` on the universal pair, and
`E ×_X V` is again weakly étale over `X`. Since every scheme mapping to `E` and `V` factors through
`E ×_X V`, and the triple products used in the cocycle condition are weakly étale over `X` too,
the axioms of a descent datum reduce to the injectivity of `rho` on pro-étale test objects.

The same datum gives the unique comparison isomorphism `pr₀^* E ≅ pr₁^* E` over `V ×_X V`
matching the two `rho`, by the Yoneda lemma on the localized site over `V ×_X V`.

Source: Stacks Project, Tags 023V, 0238 and 001P
(blueprint: lem-sfb-proetale-constant-split-descent-data, steps 5 and 6).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p] (E : Over V) [WeaklyEtale E.hom]

/-- The fibre product `E ×_X V`, as an object of the small pro-étale site of `X`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
noncomputable def overlapObj : X.ProEt :=
  ProEt.mk (pullback.snd (E.hom ≫ p) p ≫ p)

/-- The map `E ×_X V ⟶ E ⟶ V` in the small pro-étale site.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
noncomputable def overlapFst : overlapObj p E ⟶ ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.fst (E.hom ≫ p) p ≫ E.hom) (by
    simp [overlapObj, pullback.condition])

/-- The projection `E ×_X V ⟶ V` in the small pro-étale site.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
noncomputable def overlapSnd : overlapObj p E ⟶ ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.snd (E.hom ≫ p) p) rfl

variable {p E} {A : X.ProEtᵒᵖ ⥤ Type w}
  (rho : ∀ W : Over (ProEt.mk p),
    ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E) ≃
      A.obj (op W.left))

/-- The morphism `φ : E ×_X V ⟶ E` over `V` transporting the universal point of `E` along the
universal pair of points of `V` with the same image in `X`, defined through `rho`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
noncomputable def overlapTransport : pullback (E.hom ≫ p) p ⟶ E.left :=
  ((rho (Over.mk (overlapSnd p E))).symm (rho (Over.mk (overlapFst p E))
    (Over.homMk (pullback.fst (E.hom ≫ p) p) rfl))).left

@[reassoc (attr := simp)]
lemma overlapTransport_hom : overlapTransport rho ≫ E.hom = pullback.snd (E.hom ≫ p) p :=
  Over.w ((rho (Over.mk (overlapSnd p E))).symm _)

/-- **Transport preserves `rho`.** If `g : W ⟶ E ×_X V` classifies a point `f` of `E` over
`a : W ⟶ V` together with `b : W ⟶ V`, then `g ≫ φ` is a point of `E` over `b` with the same
`rho`-section as `f`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma rho_eq_of_left_eq_comp_overlapTransport
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {W : X.ProEt} (a b : W ⟶ ProEt.mk p) (f : Over.mk a.left ⟶ E) (y : Over.mk b.left ⟶ E)
    (g : W.left ⟶ pullback (E.hom ≫ p) p) (hg₁ : g ≫ pullback.fst _ _ = f.left)
    (hg₂ : g ≫ pullback.snd _ _ = b.left) (hy : y.left = g ≫ overlapTransport rho) :
    rho (Over.mk b) y = rho (Over.mk a) f := by
  let gP : W ⟶ overlapObj p E := MorphismProperty.Over.homMk g
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) hg₂).trans (MorphismProperty.Over.w b)))
  let gb : Over.mk b ⟶ Over.mk (overlapSnd p E) :=
    Over.homMk gP (MorphismProperty.Over.Hom.ext hg₂)
  let ga : Over.mk a ⟶ Over.mk (overlapFst p E) :=
    Over.homMk gP (MorphismProperty.Over.Hom.ext (by
      rw [comp_left]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ E.hom) hg₁).trans (Over.w f))))
  calc rho (Over.mk b) y
      = rho (Over.mk b) ((Over.post (ProEt.forget X) ⋙
          Over.iteratedSliceForward (Over.mk p)).map gb ≫
          (rho (Over.mk (overlapSnd p E))).symm (rho (Over.mk (overlapFst p E))
            (Over.homMk (pullback.fst (E.hom ≫ p) p) rfl))) :=
        congrArg _ (Over.OverMorphism.ext hy)
    _ = A.map gP.op (rho (Over.mk (overlapFst p E))
          (Over.homMk (pullback.fst (E.hom ≫ p) p) rfl)) := by
        rw [hrho, Equiv.apply_symm_apply]
        rfl
    _ = rho (Over.mk a) ((Over.post (ProEt.forget X) ⋙
          Over.iteratedSliceForward (Over.mk p)).map ga ≫
          Over.homMk (pullback.fst (E.hom ≫ p) p) rfl) := (hrho _ _ ga _).symm
    _ = rho (Over.mk a) f := congrArg _ (Over.OverMorphism.ext hg₁)
/-- The transport along a pair of equal points is the identity, at the level of `φ`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma lift_comp_overlapTransport_self
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {T : Scheme.{u}} (x : T ⟶ E.left) :
    pullback.lift x (x ≫ E.hom) (Category.assoc _ _ _).symm ≫ overlapTransport rho = x := by
  let δ : E.left ⟶ pullback (E.hom ≫ p) p :=
    pullback.lift (𝟙 E.left) E.hom (Category.id_comp _)
  have hδ : δ ≫ overlapTransport rho = 𝟙 E.left := by
    let c : ProEt.mk (E.hom ≫ p) ⟶ ProEt.mk p := MorphismProperty.Over.homMk E.hom rfl
    have h := rho_eq_of_left_eq_comp_overlapTransport rho hrho c c
      (Over.homMk (𝟙 E.left) (Category.id_comp _))
      (Over.homMk (δ ≫ overlapTransport rho) (by
        rw [Category.assoc, overlapTransport_hom, pullback.lift_snd]
        rfl)) δ (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) rfl
    exact congrArg (fun k ↦ k.left) ((rho (Over.mk c)).injective h)
  have hx : pullback.lift x (x ≫ E.hom) (Category.assoc _ _ _).symm = x ≫ δ := by
    ext <;> simp [δ]
  rw [hx, Category.assoc, hδ, Category.comp_id]

/-- The cocycle condition for the transport, at the level of `φ`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma lift_comp_overlapTransport_cocycle
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {T : Scheme.{u}} (x : T ⟶ E.left) (f₂ f₃ : T ⟶ V) (h₂ : x ≫ E.hom ≫ p = f₂ ≫ p)
    (h₃ : x ≫ E.hom ≫ p = f₃ ≫ p) :
    pullback.lift (pullback.lift x f₂ h₂ ≫ overlapTransport rho) f₃ (by
        rw [Category.assoc, overlapTransport_hom_assoc, pullback.lift_snd_assoc, ← h₂, h₃]) ≫
      overlapTransport rho = pullback.lift x f₃ h₃ ≫ overlapTransport rho := by
  let Q := pullback (pullback.snd (E.hom ≫ p) p ≫ p) p
  let q₁ : Q ⟶ pullback (E.hom ≫ p) p := pullback.fst _ _
  let q₂ : Q ⟶ V := pullback.snd _ _
  have hq : q₁ ≫ pullback.snd (E.hom ≫ p) p ≫ p = q₂ ≫ p := pullback.condition
  have hq' : q₁ ≫ pullback.fst (E.hom ≫ p) p ≫ E.hom ≫ p = q₂ ≫ p := by
    rw [pullback.condition, hq]
  let PQ : X.ProEt := ProEt.mk (q₂ ≫ p)
  let c₁ : PQ ⟶ ProEt.mk p := MorphismProperty.Over.homMk (q₁ ≫ pullback.fst _ _ ≫ E.hom) (by
    rw [ProEt.mk_hom, Category.assoc, Category.assoc, pullback.condition, hq]
    rfl)
  let c₂ : PQ ⟶ ProEt.mk p := MorphismProperty.Over.homMk (q₁ ≫ pullback.snd _ _) (by
    rw [ProEt.mk_hom, Category.assoc, hq]
    rfl)
  let c₃ : PQ ⟶ ProEt.mk p := MorphismProperty.Over.homMk q₂ rfl
  let x₁ : Over.mk c₁.left ⟶ E := Over.homMk (q₁ ≫ pullback.fst _ _) (Category.assoc _ _ _)
  let x₂ : Over.mk c₂.left ⟶ E := Over.homMk (q₁ ≫ overlapTransport rho) (by simp [c₂])
  have hu : pullback.lift (q₁ ≫ overlapTransport rho) q₂ (by simp [hq]) ≫
      overlapTransport rho =
        pullback.lift (q₁ ≫ pullback.fst _ _) q₂ ((Category.assoc _ _ _).trans hq') ≫
        overlapTransport rho := by
    have h₁₂ := rho_eq_of_left_eq_comp_overlapTransport rho hrho c₁ c₂ x₁ x₂ q₁ rfl rfl rfl
    have h₂₃ := rho_eq_of_left_eq_comp_overlapTransport rho hrho c₂ c₃ x₂
      (Over.homMk (pullback.lift (q₁ ≫ overlapTransport rho) q₂ (by simp [hq]) ≫
        overlapTransport rho) (by
        rw [Category.assoc, overlapTransport_hom, pullback.lift_snd]
        rfl))
      _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) rfl
    have h₁₃ := rho_eq_of_left_eq_comp_overlapTransport rho hrho c₁ c₃ x₁
      (Over.homMk (pullback.lift (q₁ ≫ pullback.fst _ _) q₂ ((Category.assoc _ _ _).trans hq') ≫
        overlapTransport rho) (by
        rw [Category.assoc, overlapTransport_hom, pullback.lift_snd]
        rfl))
      _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) rfl
    exact congrArg (fun k ↦ k.left) ((rho (Over.mk c₃)).injective
      ((h₂₃.trans h₁₂).trans h₁₃.symm))
  let m : T ⟶ Q := pullback.lift (pullback.lift x f₂ h₂) f₃ (by simp [← h₂, h₃])
  have e₁ : pullback.lift (pullback.lift x f₂ h₂ ≫ overlapTransport rho) f₃ (by
        rw [Category.assoc, overlapTransport_hom_assoc, pullback.lift_snd_assoc, ← h₂, h₃]) =
      m ≫ pullback.lift (q₁ ≫ overlapTransport rho) q₂ (by simp [hq]) := by
    ext <;> simp [m, q₁, q₂]
  have e₂ : pullback.lift x f₃ h₃ =
      m ≫ pullback.lift (q₁ ≫ pullback.fst _ _) q₂ ((Category.assoc _ _ _).trans hq') := by
    ext <;> simp [m, q₁, q₂]
  calc _ = m ≫ pullback.lift (q₁ ≫ overlapTransport rho) q₂ (by simp [hq]) ≫
        overlapTransport rho := by rw [e₁, Category.assoc]
    _ = m ≫ pullback.lift (q₁ ≫ pullback.fst _ _) q₂ ((Category.assoc _ _ _).trans hq') ≫
        overlapTransport rho := congrArg (m ≫ ·) hu
    _ = _ := by rw [← Category.assoc, ← e₂]
/-- A variant of `lift_comp_overlapTransport_self` for an arbitrary point `f` equal to `x ≫ E.hom`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma lift_comp_overlapTransport_of_hom_eq
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {T : Scheme.{u}} (x : T ⟶ E.left) (f : T ⟶ V) (hf : x ≫ E.hom = f)
    (h : x ≫ E.hom ≫ p = f ≫ p) :
    pullback.lift x f h ≫ overlapTransport rho = x := by
  subst hf
  exact lift_comp_overlapTransport_self rho hrho x

/-- Transporting a point of `E` along a pair of points of `V` and back gives the original point,
at the level of `φ`.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma lift_comp_overlapTransport_inverse
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {T : Scheme.{u}} (x : T ⟶ E.left) (f₂ : T ⟶ V) (h₂ : x ≫ E.hom ≫ p = f₂ ≫ p) :
    pullback.lift (pullback.lift x f₂ h₂ ≫ overlapTransport rho) (x ≫ E.hom) (by
        rw [Category.assoc, overlapTransport_hom_assoc, pullback.lift_snd_assoc, ← h₂,
          Category.assoc]) ≫
      overlapTransport rho = x := by
  rw [lift_comp_overlapTransport_cocycle rho hrho x f₂ (x ≫ E.hom) h₂ (Category.assoc _ _ _).symm]
  exact lift_comp_overlapTransport_self rho hrho x

/-- The descent datum on `E` relative to `p` induced by natural bijections `rho`: a point
`a : T ⟶ E` over `f₁ : T ⟶ V` is transported to `(a, f₂) ≫ φ` over `f₂`.
Source: Stacks Project, Tags 023V and 0238 (auxiliary; not a blueprint node). -/
noncomputable def descentDatumOfRho
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f)) :
    Over.DescentDatum p E where
  transport f₁ f₂ h a := Over.homMk
    (pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h) ≫ overlapTransport rho)
    (by simp)
  transport_homMk_comp g f₁ f₂ h a := by
    ext
    refine (congrArg (· ≫ overlapTransport rho) ?_).trans (Category.assoc _ _ _)
    ext <;> simp
  transport_self f a := by
    ext
    exact lift_comp_overlapTransport_of_hom_eq rho hrho a.left f (Over.w a) _
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a := by
    ext
    simp only [Over.homMk_left]
    have h₂ : a.left ≫ E.hom ≫ p = f₂ ≫ p := by rw [← Category.assoc, Over.w a]; exact h₁₂
    have h₃ : a.left ≫ E.hom ≫ p = f₃ ≫ p := h₂.trans h₂₃
    exact lift_comp_overlapTransport_cocycle rho hrho a.left f₂ f₃ h₂ h₃

lemma descentDatumOfRho_transport_left
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ V) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ E) :
    ((descentDatumOfRho rho hrho).transport f₁ f₂ h a).left =
      pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h) ≫
        overlapTransport rho :=
  rfl
/-- The transport of `descentDatumOfRho` preserves the `rho`-sections on pro-étale test objects.
Source: Stacks Project, Tag 023V (auxiliary; not a blueprint node). -/
lemma rho_descentDatumOfRho_transport
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f))
    (W : X.ProEt) (a b : W ⟶ ProEt.mk p) (f : Over.mk a.left ⟶ E) :
    rho (Over.mk b) ((descentDatumOfRho rho hrho).transport a.left b.left
      ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
      rho (Over.mk a) f :=
  rho_eq_of_left_eq_comp_overlapTransport rho hrho a b f _ _ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) rfl

/-- **Descent data from natural bijections.** If `rho` identifies the morphisms over `V` into `E`
with the sections of a presheaf `A` on the small pro-étale site of `X`, naturally on the
localized site over `V`, then there is a unique isomorphism `pr₀^* E ≅ pr₁^* E` over `V ×_X V`
matching the two `rho`, and a descent datum on `E` relative to `p` whose transport preserves
`rho`.
Source: Stacks Project, Tags 023V, 0238 and 001P
(blueprint: lem-sfb-proetale-constant-split-descent-data, steps 5 and 6). -/
theorem exists_unique_iso_and_descentDatum_of_rho
    (hrho : ∀ (W W' : Over (ProEt.mk p)) (g : W' ⟶ W)
      (f : (Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).obj W ⟶ E),
      rho W' ((Over.post (ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)).map g ≫ f) =
        A.map g.left.op (rho W f)) :
    (∃! alpha : (Over.pullback (pullback.fst p p)).obj E ≅
        (Over.pullback (pullback.snd p p)).obj E,
      ∀ (W : Over (ProEt.mk (pullback.fst p p ≫ p)))
        (f : Over.mk W.hom.left ⟶ (Over.pullback (pullback.fst p p)).obj E),
        rho ((Over.map (MorphismProperty.Over.homMk (pullback.fst p p) rfl trivial :
            ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p)).obj W)
          (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv (Over.mk W.hom.left) E).symm f) =
        rho ((Over.map (MorphismProperty.Over.homMk (pullback.snd p p)
            (pullback.condition (f := p) (g := p)).symm trivial :
            ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p)).obj W)
          (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv (Over.mk W.hom.left) E).symm
            (f ≫ alpha.hom))) ∧
    (∃ D : Over.DescentDatum p E,
      ∀ (W : X.ProEt) (a b : W ⟶ ProEt.mk p) (f : Over.mk a.left ⟶ E),
        rho (Over.mk b)
          (D.transport a.left b.left
            ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
        rho (Over.mk a) f) := by
  refine ⟨?_, descentDatumOfRho rho hrho, rho_descentDatumOfRho_transport rho hrho⟩
  have hc₁ : pullback.fst E.hom (pullback.fst p p) ≫ E.hom ≫ p =
      (pullback.snd E.hom (pullback.fst p p) ≫ pullback.snd p p) ≫ p := by
    rw [pullback.condition_assoc, Category.assoc, pullback.condition]
  have hc₂ : pullback.fst E.hom (pullback.snd p p) ≫ E.hom ≫ p =
      (pullback.snd E.hom (pullback.snd p p) ≫ pullback.fst p p) ≫ p := by
    rw [pullback.condition_assoc, Category.assoc, pullback.condition]
  let homL : pullback E.hom (pullback.fst p p) ⟶ pullback E.hom (pullback.snd p p) :=
    pullback.lift (pullback.lift _ _ hc₁ ≫ overlapTransport rho) (pullback.snd _ _) (by simp)
  let invL : pullback E.hom (pullback.snd p p) ⟶ pullback E.hom (pullback.fst p p) :=
    pullback.lift (pullback.lift _ _ hc₂ ≫ overlapTransport rho) (pullback.snd _ _) (by simp)
  have hhi : homL ≫ invL = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc,
        ← lift_comp_overlapTransport_inverse rho hrho (pullback.fst E.hom (pullback.fst p p)) _ hc₁]
      congr 1
      ext <;> simp [homL, pullback.condition]
    · simp [homL, invL]
  have hih : invL ≫ homL = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc,
        ← lift_comp_overlapTransport_inverse rho hrho (pullback.fst E.hom (pullback.snd p p)) _ hc₂]
      congr 1
      ext <;> simp [invL, pullback.condition]
    · simp [homL, invL]
  let alpha : (Over.pullback (pullback.fst p p)).obj E ≅
      (Over.pullback (pullback.snd p p)).obj E :=
    Over.isoMk ⟨homL, invL, hhi, hih⟩ (by simp [homL])
  have hcompat (W : Over (ProEt.mk (pullback.fst p p ≫ p)))
      (f : Over.mk W.hom.left ⟶ (Over.pullback (pullback.fst p p)).obj E) :
      rho ((Over.map (MorphismProperty.Over.homMk (pullback.fst p p) rfl trivial :
          ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p)).obj W)
        (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv (Over.mk W.hom.left) E).symm f) =
      rho ((Over.map (MorphismProperty.Over.homMk (pullback.snd p p)
          (pullback.condition (f := p) (g := p)).symm trivial :
          ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p)).obj W)
        (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv (Over.mk W.hom.left) E).symm
          (f ≫ alpha.hom)) := by
    refine (rho_eq_of_left_eq_comp_overlapTransport rho hrho
      (W.hom ≫ (MorphismProperty.Over.homMk (pullback.fst p p) rfl trivial :
          ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p))
      (W.hom ≫ (MorphismProperty.Over.homMk (pullback.snd p p)
          (pullback.condition (f := p) (g := p)).symm trivial :
          ProEt.mk (pullback.fst p p ≫ p) ⟶ ProEt.mk p)) _ _
      (f.left ≫ pullback.lift _ _ hc₁) ?_ ?_ ?_).symm
    · rw [Category.assoc, pullback.lift_fst]
      rfl
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc]
      exact congrArg (· ≫ pullback.snd p p) (Over.w f)
    · exact (Category.assoc _ _ _).trans (congrArg (f.left ≫ ·) (pullback.lift_fst _ _ _))
  refine ⟨alpha, hcompat, fun alpha' halpha' ↦ ?_⟩
  let W₀ : Over (ProEt.mk (pullback.fst p p ≫ p)) :=
    Over.mk (MorphismProperty.Over.homMk (pullback.snd E.hom (pullback.fst p p)) rfl trivial :
      ProEt.mk (pullback.snd E.hom (pullback.fst p p) ≫ pullback.fst p p ≫ p) ⟶
        ProEt.mk (pullback.fst p p ≫ p))
  let f₀ : Over.mk W₀.hom.left ⟶ (Over.pullback (pullback.fst p p)).obj E :=
    Over.homMk (𝟙 _) (Category.id_comp _)
  have h := (rho _).injective ((halpha' W₀ f₀).symm.trans (hcompat W₀ f₀))
  have h' := congrArg (fun k ↦ k.left)
    (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv _ _).symm.injective h)
  refine Iso.ext (Over.OverMorphism.ext ?_)
  simpa [f₀] using h'

end AlgebraicGeometry.Scheme.ProEt
