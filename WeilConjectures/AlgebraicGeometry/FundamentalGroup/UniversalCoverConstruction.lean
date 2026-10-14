/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
public import WeilConjectures.Mathlib.CategoryTheory.Galois.PointedGaloisSmall

/-!
# Construction of the universal profinite étale cover

Let `Y` be a connected scheme and `y : Spec K ⟶ Y` a geometric point, `K` separably closed. The
*universal profinite étale cover* of `Y` at `y` is the limit `Ỹ_y = lim A` over the pointed
Galois objects `(A, a)` of the Galois category `FÉt(Y)` with the fibre functor `F_y`
(SGA 1 V.5, Stacks Project Tag 0BN6; Bhatt–Scholze, *The pro-étale topology for schemes*,
§7.4). We index this limit by a small model of the (essentially small) category of pointed
Galois objects, and construct the limit as a scheme affine over `Y`
(`AlgebraicGeometry.Scheme.hasLimit_of_isAffineHom`). Its base point `ỹ : Spec K ⟶ Ỹ_y` is
given by the points `a`.

For `Y` quasi-compact and quasi-separated we show:

- `Ỹ_y ⟶ Y` is weakly étale and surjective, and `Ỹ_y` is connected;
- every finite étale `Y`-scheme `P` splits over `Ỹ_y`: the `Y`-morphisms `Ỹ_y ⟶ P` are in
  bijection with `F_y(P)` via `f ↦ ỹ ≫ f` (`AlgebraicGeometry.Scheme.UniversalCover.toObj` is
  the inverse). Surjectivity is pro-representability of `F_y`; injectivity uses that a
  morphism from a cofiltered limit of qcqs schemes to a scheme locally of finite presentation
  factors through a stage (Stacks Project Tag 01ZC), and that morphisms out of connected objects
  are determined by the image of one point.

A morphism into `Ỹ_y` is determined by its compositions with all `toObj P x`
(`AlgebraicGeometry.Scheme.UniversalCover.hom_ext`); this is how the transport and
functoriality morphisms are compared.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover

open FiniteEtale

attribute [local instance] FiniteEtale.fiberFunctor

variable {Y : Scheme.{u}} [ConnectedSpace Y] {K : Type u} [Field K] [IsSepClosed K]
  (y : Spec (.of K) ⟶ Y)

instance : EssentiallySmall.{u} (PointedGaloisObject (fiber y)) :=
  have := FiniteEtale.essentiallySmall Y
  essentiallySmall_pointedGaloisObject _

/-- The finite étale `Y`-scheme `Y` itself, as a cover. -/
noncomputable abbrev unitObj : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance, inferInstanceAs (IsFinite (𝟙 Y))⟩

instance : Nonempty (PointedGaloisObject (fiber y)) := by
  obtain ⟨A, -, a, h, -⟩ := exists_hom_from_galois_of_fiber (fiber y) unitObj
    (fiberMk y unitObj y (Category.comp_id y))
  exact ⟨⟨A, a, h⟩⟩

instance : IsCofiltered (PointedGaloisObject (fiber y)) where

/-- The small index category of the universal cover: a small model of the category of pointed
Galois objects of `F_y`. -/
abbrev Index : Type u := SmallModel.{u} (PointedGaloisObject (fiber y))

/-- The equivalence between pointed Galois objects and the index category. -/
noncomputable abbrev indexEquiv : PointedGaloisObject (fiber y) ≌ Index y :=
  equivSmallModel _

instance : IsCofiltered (Index y) := IsCofiltered.of_equivalence (indexEquiv y)

/-- The pointed Galois finite étale `Y`-schemes `A_j` indexed by `Index y`. -/
noncomputable abbrev obj : Index y ⥤ Y.FiniteEtale :=
  (indexEquiv y).inverse ⋙ PointedGaloisObject.incl _

/-- The point `a_j ∈ F_y(A_j)`. -/
noncomputable abbrev point (j : Index y) : (fiber y).obj ((obj y).obj j) :=
  ((indexEquiv y).inverse.obj j).pt

instance (j : Index y) : IsGalois ((obj y).obj j) := ((indexEquiv y).inverse.obj j).isGalois

lemma map_point {j j' : Index y} (f : j ⟶ j') :
    (fiber y).map ((obj y).map f) (point y j) = point y j' :=
  ((indexEquiv y).inverse.map f).comp

/-- The underlying diagram of schemes `j ↦ A_j`. -/
@[simps]
noncomputable def diagram : Index y ⥤ Scheme.{u} where
  obj j := ((obj y).obj j).obj.left
  map f := ((obj y).map f).hom.left
  map_id _ := by rw [CategoryTheory.Functor.map_id]; rfl
  map_comp _ _ := by rw [CategoryTheory.Functor.map_comp]; rfl

/-- The structure morphisms `A_j ⟶ Y`. -/
noncomputable abbrev p (j : Index y) : (diagram y).obj j ⟶ Y := ((obj y).obj j).obj.hom

lemma map_p {j j' : Index y} (f : j ⟶ j') : (diagram y).map f ≫ p y j' = p y j :=
  hom_left_comp _

instance (j : Index y) : IsFinite (p y j) := ((obj y).obj j).property

instance (j : Index y) : Etale (p y j) := ((obj y).obj j).obj.prop

instance {j j' : Index y} (f : j ⟶ j') : IsAffineHom ((diagram y).map f) := by
  have : IsAffineHom ((diagram y).map f ≫ p y j') := by rw [map_p]; infer_instance
  exact IsAffineHom.of_comp _ (p y j')

instance : HasLimit (diagram y) := hasLimit_of_isAffineHom _ (p y) (map_p y)

/-- The **universal profinite étale cover** `Ỹ_y = lim A_j`. -/
noncomputable abbrev cover : Scheme.{u} := limit (diagram y)

/-- A chosen index. -/
noncomputable abbrev j₀ : Index y := (IsCofiltered.nonempty (C := Index y)).some

/-- The projection `Ỹ_y ⟶ Y`. -/
noncomputable def proj : cover y ⟶ Y := limit.π (diagram y) (j₀ y) ≫ p y (j₀ y)

@[reassoc (attr := simp)]
lemma π_p (j : Index y) : limit.π (diagram y) j ≫ p y j = proj y :=
  have : CategoryTheory.IsConnected (Index y) := IsCofiltered.isConnected _
  constant_of_preserves_morphisms (fun j ↦ limit.π (diagram y) j ≫ p y j)
    (fun j j' f ↦ by
      rw [← limit.w (diagram y) f, Category.assoc, map_p]) j (j₀ y)

/-- The base point `ỹ : Spec K ⟶ Ỹ_y`, given by the points `a_j`. -/
noncomputable def pt : Spec (.of K) ⟶ cover y :=
  limit.lift (diagram y)
    { pt := Spec (.of K)
      π :=
        { app j := (point y j).left
          naturality j j' f := by
            exact (Category.id_comp _).trans
              (congrArg CommaMorphism.left (map_point y f)).symm } }

@[reassoc (attr := simp)]
lemma pt_π (j : Index y) : pt y ≫ limit.π (diagram y) j = (point y j).left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma pt_proj : pt y ≫ proj y = y := by
  rw [proj, pt_π_assoc]
  exact fiber_left_comp y _

/-- Every point of the fibre of a finite étale `Y`-scheme is the image of the point of some
`A_j`: pro-representability of the fibre functor by the pointed Galois objects. -/
lemma exists_hom_point (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    ∃ (j : Index y) (g : (obj y).obj j ⟶ P), (fiber y).map g (point y j) = x := by
  obtain ⟨A, f, a, h, hfa⟩ := exists_hom_from_galois_of_fiber (fiber y) P x
  let e := (indexEquiv y).unitIso.inv.app ⟨A, a, h⟩
  refine ⟨(indexEquiv y).functor.obj ⟨A, a, h⟩, e.val ≫ f, ?_⟩
  rw [CategoryTheory.Functor.map_comp, FintypeCat.comp_apply]
  exact (congrArg ((fiber y).map f) e.comp).trans hfa

/-- The `Y`-morphism `Ỹ_y ⟶ P` corresponding to a point `x ∈ F_y(P)`: it sends `ỹ` to `x`. -/
noncomputable def toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) : cover y ⟶ P.obj.left :=
  limit.π (diagram y) (exists_hom_point y P x).choose ≫
    (exists_hom_point y P x).choose_spec.choose.hom.left

@[reassoc (attr := simp)]
lemma toObj_hom (P : Y.FiniteEtale) (x : (fiber y).obj P) :
    toObj y P x ≫ P.obj.hom = proj y := by
  rw [toObj, Category.assoc, hom_left_comp]
  exact π_p y _

@[reassoc (attr := simp)]
lemma pt_toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) : pt y ≫ toObj y P x = x.left := by
  rw [toObj, pt_π_assoc, ← fiber_map_left, (exists_hom_point y P x).choose_spec.choose_spec]


/-- The structure morphisms `A_j ⟶ Y` as a natural transformation to the constant diagram. -/
noncomputable def pNatTrans : diagram y ⟶ (Functor.const (Index y)).obj Y where
  app := p y
  naturality _ _ f := (map_p y f).trans (Category.comp_id _).symm

/-- `Ỹ_y` is weakly étale over `Y`: it is a cofiltered limit of affine étale `Y`-schemes. -/
instance weaklyEtale_proj : WeaklyEtale (proj y) :=
  weaklyEtale_of_isLimit (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)

/-- `Ỹ_y` is surjective over `Y`: the `A_j` are nonempty finite étale over the connected `Y`. -/
lemma surjective_proj : Function.Surjective (proj y) :=
  surjective_of_isLimit (diagram y) (limit.isLimit _) (p y) (map_p y) (proj y) (π_p y)
    fun j ↦ (surjective_of_nonempty_fiber y ((obj y).obj j) ⟨point y j⟩).surj

section QCQS

variable [CompactSpace Y] [QuasiSeparatedSpace Y]

instance (j : Index y) : CompactSpace ((diagram y).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (p y j)

instance (j : Index y) : QuasiSeparatedSpace ((diagram y).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (p y j)

/-- `Ỹ_y` is connected: it is a cofiltered limit of the connected qcqs schemes `A_j`. -/
instance connectedSpace_cover : ConnectedSpace (cover y) :=
  have (j : Index y) : ConnectedSpace ((diagram y).obj j) :=
    connectedSpace_of_isConnected ((obj y).obj j)
  connectedSpace_of_isLimit (diagram y) (limit.isLimit _)

/-- A `Y`-morphism from `Ỹ_y` to a finite étale `Y`-scheme factors through some `A_j`
(Stacks Project Tag 01ZC, `Hom_Y(lim A_j, P) = colim Hom_Y(A_j, P)` for `P` locally of finite
presentation). -/
lemma exists_factor (P : Y.FiniteEtale) (f : cover y ⟶ P.obj.left)
    (hf : f ≫ P.obj.hom = proj y) :
    ∃ (j : Index y) (g : (obj y).obj j ⟶ P), limit.π (diagram y) j ≫ g.hom.left = f := by
  have : Etale P.obj.hom := P.obj.prop
  obtain ⟨j, g, hg, hgp⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (diagram y) (pNatTrans y) P.obj.hom (limit.cone _) (limit.isLimit _) f (by
      ext j
      simp [pNatTrans, hf])
  exact ⟨j, ObjectProperty.homMk (MorphismProperty.Over.homMk g hgp), hg⟩

/-- Two `Y`-morphisms from `Ỹ_y` to a finite étale `Y`-scheme agreeing at `ỹ` are equal. -/
lemma eq_of_pt_comp_eq (P : Y.FiniteEtale) {f₁ f₂ : cover y ⟶ P.obj.left}
    (h₁ : f₁ ≫ P.obj.hom = proj y) (h₂ : f₂ ≫ P.obj.hom = proj y) (h : pt y ≫ f₁ = pt y ≫ f₂) :
    f₁ = f₂ := by
  obtain ⟨i₁, g₁, rfl⟩ := exists_factor y P f₁ h₁
  obtain ⟨i₂, g₂, rfl⟩ := exists_factor y P f₂ h₂
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i₁ i₂
  have e₁ : limit.π (diagram y) i₁ ≫ g₁.hom.left =
      limit.π (diagram y) k ≫ ((obj y).map a ≫ g₁).hom.left := by
    rw [← limit.w (diagram y) a, Category.assoc]
    rfl
  have e₂ : limit.π (diagram y) i₂ ≫ g₂.hom.left =
      limit.π (diagram y) k ≫ ((obj y).map b ≫ g₂).hom.left := by
    rw [← limit.w (diagram y) b, Category.assoc]
    rfl
  rw [e₁, e₂] at h ⊢
  have : (obj y).map a ≫ g₁ = (obj y).map b ≫ g₂ := by
    refine evaluation_injective_of_isConnected (fiber y) _ P (point y k) (fiber_ext y ?_)
    change (point y k).left ≫ _ = (point y k).left ≫ _
    rw [← pt_π_assoc, ← pt_π_assoc]
    exact h
  rw [this]

/-- `toObj P x` is the unique `Y`-morphism `Ỹ_y ⟶ P` sending `ỹ` to `x`. -/
lemma eq_toObj (P : Y.FiniteEtale) (x : (fiber y).obj P) (f : cover y ⟶ P.obj.left)
    (hf : f ≫ P.obj.hom = proj y) (hx : pt y ≫ f = x.left) : f = toObj y P x :=
  eq_of_pt_comp_eq y P hf (toObj_hom y P x) (by rw [hx, pt_toObj])

/-- The projection to a stage `A_j`, followed by a morphism `A_j ⟶ P`, is `toObj`. -/
lemma π_comp_eq_toObj (j : Index y) {P : Y.FiniteEtale} (g : (obj y).obj j ⟶ P) :
    limit.π (diagram y) j ≫ g.hom.left = toObj y P ((fiber y).map g (point y j)) :=
  eq_toObj y P _ _ (by rw [Category.assoc, hom_left_comp]; exact π_p y j)
    (by rw [pt_π_assoc, fiber_map_left])

/-- The projection to a stage `A_j` is `toObj A_j a_j`. -/
lemma π_eq_toObj (j : Index y) :
    limit.π (diagram y) j = toObj y ((obj y).obj j) (point y j) := by
  refine (Category.comp_id _).symm.trans ((π_comp_eq_toObj y j (𝟙 _)).trans ?_)
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `toObj` is natural in the finite étale `Y`-scheme. -/
@[reassoc]
lemma toObj_comp {P Q : Y.FiniteEtale} (g : P ⟶ Q) (x : (fiber y).obj P) :
    toObj y P x ≫ g.hom.left = toObj y Q ((fiber y).map g x) :=
  eq_toObj y Q _ _ (by rw [Category.assoc, hom_left_comp, toObj_hom])
    (by rw [pt_toObj_assoc, fiber_map_left])

/-- **Morphisms into `Ỹ_y` are determined by their compositions with all `toObj P x`.** -/
lemma hom_ext {T : Scheme.{u}} {h₁ h₂ : T ⟶ cover y}
    (h : ∀ (P : Y.FiniteEtale) (x : (fiber y).obj P), h₁ ≫ toObj y P x = h₂ ≫ toObj y P x) :
    h₁ = h₂ :=
  limit.hom_ext fun j ↦ by rw [π_eq_toObj]; exact h _ _

/-- **Every finite étale `Y`-scheme splits over `Ỹ_y`**: `f ↦ ỹ ≫ f` is a bijection between
`Hom_Y(Ỹ_y, P)` and `F_y(P)`. -/
theorem bijective_fiber (P : Y.FiniteEtale) :
    Function.Bijective fun f : {f : cover y ⟶ P.obj.left // f ≫ P.obj.hom = proj y} ↦
      fiberMk y P (pt y ≫ f.1) (by rw [Category.assoc, f.2]; exact pt_proj y) :=
  ⟨fun f₁ f₂ h ↦ Subtype.ext (eq_of_pt_comp_eq y P f₁.2 f₂.2 (congrArg CommaMorphism.left h)),
    fun x ↦ ⟨⟨toObj y P x, toObj_hom y P x⟩, fiber_ext y (pt_toObj y P x)⟩⟩

end QCQS

end AlgebraicGeometry.Scheme.UniversalCover
