/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Fixed-object coproducts and their canonical pushout comparison

Source: Dwyer--Kan, *Simplicial localizations of categories*, Sections 7.4--7.6
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct).

`Functor` specializes an ordinary functor to the identity object function. The category
instance lets us use Mathlib's `BinaryCofan`, `IsColimit`, `IsPushout` and `Iso` directly.
There is no separate definition of a coproduct, pushout or isomorphism here.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace FixedObject

/-- An ordinary functor with the identity object function; its map has unchanged endpoints.
Source: Dwyer--Kan, Sections 7.4--7.6
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct). -/
structure Functor (O : Type u) (A B : Category.{v} O) where
  map : ∀ {x y : O}, A.Hom x y → B.Hom x y
  map_id : ∀ x : O, map (A.id x) = B.id x
  map_comp : ∀ {x y z : O} (f : A.Hom x y) (g : A.Hom y z),
    map (A.comp f g) = B.comp (map f) (map g)

/-- Identity functor fixing objects. Source: Dwyer--Kan, Sections 7.4--7.6
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct). -/
def Functor.id {O : Type u} {A : Category.{v} O} : Functor O A A where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of functors fixing objects. Source: Dwyer--Kan, Sections 7.4--7.6
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct). -/
def Functor.comp {O : Type u} {A B C : Category.{v} O}
    (F : Functor O A B) (G : Functor O B C) : Functor O A C where
  map f := G.map (F.map f)
  map_id x := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

/-- The category of categories on `O` and functors fixing `O`.
Source: Dwyer--Kan, Sections 7.4--7.6
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct). -/
instance fixedCategory (O : Type u) : Category (Category.{v} O) where
  Hom A B := Functor O A B
  id := fun _ ↦ Functor.id
  comp F G := F.comp G
  id_comp F := by cases F; rfl
  comp_id F := by cases F; rfl
  assoc F G H := by cases F; cases G; cases H; rfl

/-- The canonical comparison `F *_O V → P`, defined by its two coproduct restrictions.
Its data comes from the actual colimit eliminator, not from a postponed existence proof.
Source: Dwyer--Kan, Sections 7.4--7.6; Stacks Tag 002J
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct). -/
def pushoutComparison {O : Type u} {F A V P : Category.{v} O}
    (cFA : BinaryCofan F A) (cFV : BinaryCofan F V) (hcFV : IsColimit cFV)
    (a : cFA.pt ⟶ P) (b : V ⟶ P) : cFV.pt ⟶ P :=
  BinaryCofan.IsColimit.desc hcFV (cFA.inl ≫ a) b

/-- The canonical fixed-object coproduct/pushout comparison is an isomorphism, with the
specified restrictions of the inverse on both pushout structure maps.

Source: Dwyer--Kan, Sections 7.4--7.6; Mathlib's
`CategoryTheory.IsPushout.of_coprod_inl_with_id`, transported along coproduct braiding
(blueprint: lem-coef-fixed-object-scat-pushout-coproduct).

Proof: the coproduct property constructs the map from `F *_O V` to `P` with restrictions
`F → F *_O A → P` and `b`. In the other direction the map from `F *_O A` restricts to the
`F` inclusion and to `v` followed by the `V` inclusion. These maps agree on `A`, so the
pushout property extends them to `P`. The two composites are identities: on `F,V` this is
the coproduct uniqueness, and on `F *_O A,V` it is pushout uniqueness. The displayed
restrictions follow from those same universal properties. In particular, maps from `P`
to a category on `O` are exactly pairs of maps from `F,V` fixing `O`. -/
theorem fixed_object_scat_pushout_coproduct {O : Type u}
    (F A V P : Category.{v} O) (v : A ⟶ V)
    (cFA : BinaryCofan F A) (hcFA : IsColimit cFA)
    (cFV : BinaryCofan F V) (hcFV : IsColimit cFV)
    (a : cFA.pt ⟶ P) (b : V ⟶ P) (p : IsPushout cFA.inr v a b) :
    ∃ e : cFV.pt ≅ P,
      e.hom = pushoutComparison cFA cFV hcFV a b ∧
      a ≫ e.inv = BinaryCofan.IsColimit.desc hcFA cFV.inl (v ≫ cFV.inr) ∧
      b ≫ e.inv = cFV.inr := by
  sorry

end FixedObject

end
