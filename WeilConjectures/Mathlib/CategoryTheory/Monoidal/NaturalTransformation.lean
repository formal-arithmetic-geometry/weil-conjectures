/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transporting a lax monoidal structure is monoidal

We show that the natural isomorphism along which a lax monoidal structure is transported
in `CategoryTheory.Functor.LaxMonoidal.transport` is a monoidal natural transformation.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Transporting a lax monoidal structure along a natural isomorphism of functors makes the
isomorphism a monoidal natural transformation. -/
lemma natTransIsMonoidal_of_transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    i.hom.IsMonoidal := by
  let := transport i
  refine ⟨rfl, fun X Y ↦ ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

end CategoryTheory.Functor.LaxMonoidal
