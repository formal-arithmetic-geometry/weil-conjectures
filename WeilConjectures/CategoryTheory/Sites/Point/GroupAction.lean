/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Sites.Point.Category

/-!
# Points of a site with a group action

Let `Φ` be a point of a site `(C, J)` and let a group `G` act on its fibre functor
`Φ.fiber`, i.e. we are given a monoid map `act : G →* End Φ.fiber`. Then `G` acts on the fibre
`Φ.sheafFiber.obj F` of every abelian sheaf `F`, by `[X, x, t] ↦ [X, σ • x, t]`; this defines a
functor `Φ.sheafFiberAction act : Sheaf J Ab ⥤ Action Ab G`.

This functor has a right adjoint `Φ.equivariantSheafFunctor act`, sending `M` to the sheaf of
`G`-equivariant maps `X ↦ {f : Φ.fiber.obj X → M | f (σ • x) = σ • f x}`: a subsheaf of the
skyscraper sheaf at `Φ` with value `M`.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.sheafFiberAction`: the fibre functor with its
  `G`-action.
- `CategoryTheory.GrothendieckTopology.Point.equivariantSheafFunctor`: the sheaves of
  equivariant maps.
- `CategoryTheory.GrothendieckTopology.Point.sheafFiberActionAdjunction`: the adjunction.
-/

@[expose] public section

universe w v u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {G : Type u'} [Group G] (act : G →* End Φ.fiber)

/-- The endomorphism of the point `Φ` given by the action of `σ` on its fibre functor. -/
def actHom (σ : G) : Φ ⟶ Φ :=
  ⟨act σ⟩

/-- The action of `σ` on the fibre of a presheaf: `[X, x, t] ↦ [X, σ • x, t]`. -/
noncomputable def presheafFiberAct (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) :
    Φ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj P :=
  (Hom.presheafFiber (Φ.actHom act σ)).app P

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberAct (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) (X : C)
    (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiberAct act P σ =
      Φ.toPresheafFiber X ((act σ).app X x) P := by
  simp [presheafFiberAct, actHom]

lemma toPresheafFiber_presheafFiberAct_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) (X : C)
    (x : Φ.fiber.obj X) (t : P.obj (op X)) :
    (Φ.presheafFiberAct act P σ).hom (Φ.toPresheafFiber X x P t) =
      Φ.toPresheafFiber X ((act σ).app X x) P t :=
  congr($(Φ.toPresheafFiber_presheafFiberAct act P σ X x).hom t)

lemma act_mul_app (σ τ : G) (X : C) (x : Φ.fiber.obj X) :
    (act (σ * τ)).app X x = (act σ).app X ((act τ).app X x) := by
  rw [map_mul, End.mul_def]
  rfl

@[simp]
lemma act_one_app (X : C) (x : Φ.fiber.obj X) : (act 1).app X x = x := by
  rw [map_one, End.one_def]
  rfl

/-- The fibre of a presheaf, with its action of `G`. -/
noncomputable abbrev presheafFiberAction (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Action AddCommGrpCat.{w} G where
  V := Φ.presheafFiber.obj P
  ρ :=
    { toFun σ := Φ.presheafFiberAct act P σ
      map_one' := by
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [toPresheafFiber_presheafFiberAct, act_one_app, End.one_def, Category.comp_id]
      map_mul' σ τ := by
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [toPresheafFiber_presheafFiberAct, End.mul_def, toPresheafFiber_presheafFiberAct_assoc,
          toPresheafFiber_presheafFiberAct, act_mul_app] }

@[simp]
lemma presheafFiberAction_V (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (Φ.presheafFiberAction act P).V = Φ.presheafFiber.obj P :=
  rfl

@[simp]
lemma presheafFiberAction_ρ (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) :
    (Φ.presheafFiberAction act P).ρ σ = Φ.presheafFiberAct act P σ :=
  rfl

/-- The fibre functor on abelian sheaves, with the action of `G` on the fibres. -/
@[simps]
noncomputable def sheafFiberAction : Sheaf J AddCommGrpCat.{w} ⥤ Action AddCommGrpCat.{w} G where
  obj F := Φ.presheafFiberAction act F.obj
  map {F F'} f :=
    { hom := Φ.presheafFiber.map f.hom
      comm σ := by
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [presheafFiberAction_ρ, presheafFiberAction_ρ, toPresheafFiber_presheafFiberAct_assoc]
        rw [toPresheafFiber_naturality]
        rw [toPresheafFiber_naturality_assoc, toPresheafFiber_presheafFiberAct] }

section equivariant

variable (M : Action AddCommGrpCat.{w} G)

/-- The `G`-equivariant maps `Φ.fiber.obj X → M`. -/
def equivariantMaps (X : C) : AddSubgroup (Φ.fiber.obj X → M.V) where
  carrier := {f | ∀ (σ : G) (x : Φ.fiber.obj X), f ((act σ).app X x) = (M.ρ σ).hom (f x)}
  zero_mem' σ x := by simp
  add_mem' {f g} hf hg σ x := by simp [hf σ x, hg σ x]
  neg_mem' {f} hf σ x := by simp [hf σ x]

lemma mem_equivariantMaps {X : C} (f : Φ.fiber.obj X → M.V) :
    f ∈ Φ.equivariantMaps act M X ↔
      ∀ (σ : G) (x : Φ.fiber.obj X), f ((act σ).app X x) = (M.ρ σ).hom (f x) :=
  Iff.rfl

/-- Precomposition with `Φ.fiber.map g` on equivariant maps. -/
def equivariantMapsComap {X Y : C} (g : Y ⟶ X) :
    Φ.equivariantMaps act M X →+ Φ.equivariantMaps act M Y where
  toFun f := ⟨fun y ↦ f.1 (Φ.fiber.map g y), fun σ y ↦ by
    rw [← f.2 σ, ← NatTrans.naturality_apply]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma equivariantMapsComap_apply_coe {X Y : C} (g : Y ⟶ X) (f : Φ.equivariantMaps act M X)
    (y : Φ.fiber.obj Y) :
    (Φ.equivariantMapsComap act M g f).1 y = f.1 (Φ.fiber.map g y) :=
  rfl

/-- The presheaf of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (Φ.equivariantMaps act M X.unop)
  map g := AddCommGrpCat.ofHom (Φ.equivariantMapsComap act M g.unop)
  map_id X := by
    ext f
    exact Subtype.ext (funext fun x ↦ by simp)
  map_comp f g := by
    ext h
    exact Subtype.ext (funext fun x ↦ by simp)

lemma equivariantPresheaf_map_apply_coe {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (f : (Φ.equivariantPresheaf act M).obj X) (y : Φ.fiber.obj Y.unop) :
    ((Φ.equivariantPresheaf act M).map g f).1 y = f.1 (Φ.fiber.map g.unop y) :=
  rfl

/-- Two elements of the fibre over `X` coming from the fibres over two objects of a covering
sieve also come from a common object of that sieve. -/
lemma exists_of_fiber_map_eq {X Y₁ Y₂ : C} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (y₁ : Φ.fiber.obj Y₁)
    (y₂ : Φ.fiber.obj Y₂) (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
    ∃ (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
      Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
  let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₁, rfl⟩
  let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₂, h.symm⟩
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  rw [Subtype.ext_iff] at fac
  exact ⟨z.1, q₁.1, q₂.1, z.2, fac, q₁.2, q₂.2⟩

lemma isSheaf_equivariantPresheaf : Presheaf.IsSheaf J (Φ.equivariantPresheaf act M) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR s hs
  -- the value at `x` of the amalgamation, computed from any lift of `x` to the sieve
  have key {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂)
      (y₁ : Φ.fiber.obj Y₁) (y₂ : Φ.fiber.obj Y₂)
      (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
      (s f₁ h₁).1 y₁ = (s f₂ h₂).1 y₂ := by
    obtain ⟨Z, p₁, p₂, z, fac, rfl, rfl⟩ := Φ.exists_of_fiber_map_eq f₁ f₂ y₁ y₂ h
    exact congr_arg (fun g ↦ (Subtype.val g) z) (hs p₁ p₂ h₁ h₂ fac)
  choose Y f hf y hy using fun x ↦ Φ.jointly_surjective R hR x
  have hval {Y' : C} {f' : Y' ⟶ X} (h' : R f') (y' : Φ.fiber.obj Y') :
      (s (f (Φ.fiber.map f' y')) (hf _)).1 (y _) = (s f' h').1 y' :=
    key _ _ _ _ (hy _)
  let t : (Φ.equivariantPresheaf act M ⋙ forget AddCommGrpCat.{w}).obj (op X) :=
    ⟨fun x ↦ (s (f x) (hf x)).1 (y x), fun σ x ↦ by
      have := hval (hf x) ((act σ).app _ (y x))
      rw [← FunctorToTypes.naturality, hy] at this
      rw [this, (s (f x) (hf x)).2 σ (y x)]⟩
  refine ⟨t, fun Y' f' h' ↦ Subtype.ext (funext fun y' ↦ hval h' y'), fun t' ht' ↦ ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  have := congr_arg (fun g ↦ (Subtype.val g) (y x)) (ht' (f x) (hf x))
  simp only at this
  rw [← this]
  change t'.1 x = t'.1 (Φ.fiber.map (f x) (y x))
  rw [hy]

/-- The sheaf of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantSheaf : Sheaf J AddCommGrpCat.{w} :=
  ⟨Φ.equivariantPresheaf act M, Φ.isSheaf_equivariantPresheaf act M⟩

end equivariant

/-- The functor sending `M` to the sheaf of `G`-equivariant maps from the fibres of `Φ`
to `M`. -/
@[simps]
def equivariantSheafFunctor : Action AddCommGrpCat.{w} G ⥤ Sheaf J AddCommGrpCat.{w} where
  obj M := Φ.equivariantSheaf act M
  map {M N} φ := ⟨{
    app X := AddCommGrpCat.ofHom
      { toFun f := ⟨fun x ↦ φ.hom.hom (f.1 x), fun σ x ↦ by
          rw [f.2 σ x]
          exact congr($(φ.comm σ).hom (f.1 x))⟩
        map_zero' := by ext; simp
        map_add' _ _ := by ext; simp }
    naturality _ _ _ := rfl }⟩

/-- The unit of the adjunction: a section `t` over `X` gives the equivariant map
`x ↦ [X, x, t]`. -/
@[simps]
noncomputable def toEquivariantSheaf (F : Sheaf J AddCommGrpCat.{w}) :
    F ⟶ Φ.equivariantSheaf act ((Φ.sheafFiberAction act).obj F) :=
  ⟨{app X := AddCommGrpCat.ofHom
      { toFun t := ⟨fun x ↦ Φ.toPresheafFiber X.unop x F.obj t, fun σ x ↦ by
          simp [toPresheafFiber_presheafFiberAct_apply]⟩
        map_zero' := by ext; simp
        map_add' _ _ := by ext; simp }
    naturality X Y g := by
      ext t
      refine Subtype.ext (funext fun y ↦ ?_)
      simp [equivariantPresheaf_map_apply_coe] }⟩

/-- The counit of the adjunction: `[X, x, f] ↦ f x`. -/
noncomputable def fromEquivariantSheaf (M : Action AddCommGrpCat.{w} G) :
    (Φ.sheafFiberAction act).obj (Φ.equivariantSheaf act M) ⟶ M where
  hom := Φ.presheafFiberDesc
    (fun X x ↦ AddCommGrpCat.ofHom
      { toFun f := f.1 x
        map_zero' := rfl
        map_add' _ _ := rfl })
    (fun X Y g x ↦ by
      ext f
      rfl)
  comm σ := by
    refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
    ext f
    simp only [sheafFiberAction_obj, presheafFiberAction_ρ, MonoidHom.coe_mk, OneHom.coe_mk,
      toPresheafFiber_presheafFiberAct_assoc, toPresheafFiber_presheafFiberDesc,
      toPresheafFiber_presheafFiberDesc_assoc]
    exact f.2 σ x

@[simp]
lemma toPresheafFiber_fromEquivariantSheaf_hom_apply (M : Action AddCommGrpCat.{w} G) (X : C)
    (x : Φ.fiber.obj X) (f : (Φ.equivariantPresheaf act M).obj (op X)) :
    (Φ.fromEquivariantSheaf act M).hom.hom (Φ.toPresheafFiber X x _ f) = f.1 x :=
  congr($(Φ.toPresheafFiber_presheafFiberDesc _ _ X x).hom f)

/-- The fibre functor with its `G`-action is left adjoint to the sheaf of equivariant maps. -/
noncomputable def sheafFiberActionAdjunction :
    Φ.sheafFiberAction act ⊣ Φ.equivariantSheafFunctor act :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app F := Φ.toEquivariantSheaf act F
          naturality {F F'} g := by
            ext X t
            refine Subtype.ext (funext fun x ↦ ?_)
            simp }
      counit :=
        { app M := Φ.fromEquivariantSheaf act M
          naturality {M N} φ := by
            ext : 1
            refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
            ext f
            simp }
      left_triangle := by
        ext F : 3
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        ext t
        simp
      right_triangle := by
        ext M X f : 4
        refine Subtype.ext (funext fun x ↦ ?_)
        simp }

end CategoryTheory.GrothendieckTopology.Point
