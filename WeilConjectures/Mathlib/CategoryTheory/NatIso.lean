/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# Invertibility of a natural transformation at an object is invariant under isomorphism

This file records the observation that whether a natural transformation is invertible at an
object only depends on the isomorphism class of that object. It is the form in which
`AlgebraicGeometry.Etale.isIso_of_isIso_openImmersionRestriction` transports invertibility
of a morphism of sheaves from an étale `U`-scheme to an isomorphic étale `X`-scheme.

## Main results

- `CategoryTheory.NatTrans.isIso_app_of_iso`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]

/-- Invertibility of a natural transformation at an object only depends on the object up to
isomorphism. -/
lemma NatTrans.isIso_app_of_iso {F G : C ⥤ A} (φ : F ⟶ G) {X Y : C} (e : X ≅ Y)
    [IsIso (φ.app Y)] : IsIso (φ.app X) := by
  have key : φ.app X = F.map e.hom ≫ φ.app Y ≫ inv (G.map e.hom) := by
    rw [← Category.assoc, φ.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

end CategoryTheory
