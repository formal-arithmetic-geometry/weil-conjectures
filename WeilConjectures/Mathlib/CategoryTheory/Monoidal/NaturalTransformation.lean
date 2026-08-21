/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidality of the isomorphism along which a lax monoidal structure is transported

If `F G : C ⥤ D` are functors between monoidal categories, `F` is lax monoidal and
`i : F ≅ G`, then with respect to the transported lax monoidal structure
`CategoryTheory.Functor.LaxMonoidal.transport i` on `G`, the natural transformation
`i.hom` is monoidal (`CategoryTheory.Functor.LaxMonoidal.transport_isMonoidal_hom`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- With respect to a lax monoidal structure transported along a natural isomorphism `i`,
the natural transformation `i.hom` is monoidal. -/
lemma transport_isMonoidal_hom {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    NatTrans.IsMonoidal i.hom := by
  letI := transport i
  refine ⟨rfl, fun X Y ↦ ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

end CategoryTheory.Functor.LaxMonoidal
