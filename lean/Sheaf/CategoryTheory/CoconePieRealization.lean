/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF stage-2 worker NC
-/
module

public import Sheaf.CategoryTheory.Inserter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Cocones as an equifier in an inserter

Source: the blueprint, `sec-six-functors`, proof of
`prop-coef-integral-exceptional-adjoint`, categorical cocone construction in the
complete-implies-cocomplete argument (blueprint: lem-coef-cocone-pie-realization).
The canonical comparison retains the vertex, every leg, and every underlying morphism.
-/

@[expose] public section

universe w u

namespace CategoryTheory.Limits.CoconePIE

variable {J : Type w} [SmallCategory J] {A : Type u} [Category.{w} A]

/-- The constant functor with value the object-indexed family of diagram values.
Source: blueprint, exceptional-adjoint proof, cocone construction
(blueprint: lem-coef-cocone-pie-realization). -/
def constantFamily (D : J ⥤ A) : A ⥤ (J → A) :=
  (Functor.const A).obj D.obj

/-- The diagonal functor into a product indexed by a type, including the empty type.
Source: blueprint, exceptional-adjoint proof, cocone construction
(blueprint: lem-coef-cocone-pie-realization). -/
def diagonal (S : Type w) (A : Type u) [Category.{w} A] : A ⥤ (S → A) :=
  Functor.pi' (fun _ : S ↦ 𝟭 A)

/-- The constant functor on the inserter, indexed by all arrows of the diagram's shape.
Source: blueprint, exceptional-adjoint proof, cocone construction
(blueprint: lem-coef-cocone-pie-realization). -/
def arrowSources (D : J ⥤ A) :
    Inserter (constantFamily D) (diagonal J A) ⥤ (Arrow J → A) :=
  (Functor.const (Inserter (constantFamily D) (diagonal J A))).obj
    (fun a : Arrow J ↦ D.obj a.left)

/-- The diagonal of the vertex projection, indexed by all arrows of the diagram's shape.
Source: blueprint, exceptional-adjoint proof, cocone construction
(blueprint: lem-coef-cocone-pie-realization). -/
def arrowVertices (D : J ⥤ A) :
    Inserter (constantFamily D) (diagonal J A) ⥤ (Arrow J → A) :=
  Inserter.forget (constantFamily D) (diagonal J A) ⋙ diagonal (Arrow J) A

/-- Forget cocone compatibility while retaining the vertex, legs, and underlying morphisms.
Source: blueprint, exceptional-adjoint proof, cocone identification
(blueprint: lem-coef-cocone-pie-realization). -/
def coconeToInserter (D : J ⥤ A) :
    Cocone D ⥤ Inserter (constantFamily D) (diagonal J A) where
  obj c := ⟨c.pt, fun j ↦ c.ι.app j⟩
  map f :=
    { hom := f.hom
      w := funext (fun j ↦ by
        simp [constantFamily, diagonal]) }
  map_id c := Inserter.Hom.ext (by rfl)
  map_comp f g := Inserter.Hom.ext (by rfl)

/-- Cocones are canonically the equifier inside the specified inserter, with transformations
whose arrow coordinates are respectively `D.map a.hom ≫ u a.right` and `u a.left`.
The equality of functors specifies the canonical comparison on both objects and morphisms.

Source: blueprint, exceptional-adjoint proof, complete implies cocomplete, explicit
cocone identification (blueprint: lem-coef-cocone-pie-realization).

Proof: (1) Products are coordinatewise. Thus the inserter consists of vertices `X` with
legs `u j : D.obj j ⟶ X`; its arrow equation is precisely `u j ≫ h = v j`, as in
`def-coef-inserter`. (2) Set the two components at an arrow `a` equal to
`D.map a.hom ≫ u a.right` and `u a.left`. The inserter arrow equation proves naturality
of both families. (3) Equality of these components is exactly cocone compatibility in
`def-weil-pbc-category-colimit`. Turn a compatible family into its cocone, retaining the
vertex and legs, and retain the underlying arrow on morphisms. Fullness means there is
no further arrow condition. The inverse forgets compatibility via `coconeToInserter`;
the composites are identities up to the canonical identity-component isomorphisms.
(4) For empty `J`, both index types are empty, all equations are vacuous, and both
categories consist of arbitrary vertices and their morphisms. -/
theorem cocone_pie_realization (D : J ⥤ A) :
    ∃ α β : arrowSources D ⟶ arrowVertices D,
      (∀ (X : Inserter (constantFamily D) (diagonal J A)) (a : Arrow J),
        α.app X a = D.map a.hom ≫ X.hom a.right ∧ β.app X a = X.hom a.left) ∧
      ∃ e : (ObjectProperty.FullSubcategory
          (fun X : Inserter (constantFamily D) (diagonal J A) ↦ α.app X = β.app X)) ≌
          Cocone D,
        e.inverse ⋙ ObjectProperty.ι
          (fun X : Inserter (constantFamily D) (diagonal J A) ↦ α.app X = β.app X) =
          coconeToInserter D := by
  sorry

end CategoryTheory.Limits.CoconePIE
