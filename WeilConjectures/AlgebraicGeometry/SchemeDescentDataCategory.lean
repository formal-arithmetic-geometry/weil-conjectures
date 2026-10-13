/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# The category of scheme descent data

Source: Stacks Project, Descent, Definition 023V(3).
(blueprint: def-galois-scheme-descent-data-category).

These are the unchanged category definitions extracted from FpqcSingletonFullyFaithful,
so independent proof steps may use them without importing the theorem they prove.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace CategoryTheory

namespace Over

/-- Objects of the category of descent data relative to `X/S`, in the transport form of
`Over.DescentDatum`. Source: Stacks Project, Descent, Definition 35.34.1 (Tag 023V)
(blueprint: def-galois-scheme-descent-data-category). -/
structure DescentDataCategory {S X : Scheme.{u}} (a : X ⟶ S) where
  V : Over X
  datum : DescentDatum a V

namespace DescentDataCategory

variable {S X : Scheme.{u}} {a : X ⟶ S}

/-- Morphisms over `X` compatible with the two descent data. Source: Stacks Project,
Descent, Definition 35.34.1 (3) (Tag 023V)
(blueprint: def-galois-scheme-descent-data-category). -/
@[ext]
structure Hom (A B : DescentDataCategory a) where
  hom : A.V ⟶ B.V
  commutes : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
    (z : Over.mk f₀ ⟶ A.V),
    B.datum.transport f₀ f₁ h (z ≫ hom) =
      A.datum.transport f₀ f₁ h z ≫ hom

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
