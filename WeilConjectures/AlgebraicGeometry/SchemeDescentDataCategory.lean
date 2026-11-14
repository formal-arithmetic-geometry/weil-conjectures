/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# The category of descent data along a morphism of schemes

Objects are objects of `Over X` with a descent datum along `a : X ⟶ S`; morphisms are maps in
`Over X` compatible with the transport maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace CategoryTheory

namespace Over

/-- The objects of the category of descent data along `a : X ⟶ S`: an object `V` of `Over X`
together with a descent datum on it. -/
structure DescentDataCategory {S X : Scheme.{u}} (a : X ⟶ S) where
  V : Over X
  datum : DescentDatum a V

namespace DescentDataCategory

variable {S X : Scheme.{u}} {a : X ⟶ S}

/-- A morphism of descent data: a morphism in `Over X` compatible with the transport maps. -/
@[ext]
structure Hom (A B : DescentDataCategory a) where
  hom : A.V ⟶ B.V
  commutes : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
    (z : Over.mk f₀ ⟶ A.V),
    B.datum.transport f₀ f₁ h (z ≫ hom) =
      A.datum.transport f₀ f₁ h z ≫ hom

/-- Descent data along `a` form a category, with composition and identities given by those of
`Over X`. -/
instance : Category (DescentDataCategory a) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.V
      commutes := by
        intro T f₀ f₁ h z
        simp only [Category.comp_id] }
  comp := fun {A B C} f g =>
    { hom := f.hom ≫ g.hom
      commutes := by
        intro T i j h z
        change C.datum.transport i j h ((z ≫ f.hom) ≫ g.hom) =
          (A.datum.transport i j h z ≫ f.hom) ≫ g.hom
        rw [g.commutes, f.commutes] }
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end DescentDataCategory

end Over

end CategoryTheory
