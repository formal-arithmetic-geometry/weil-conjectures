/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSmallGenerator

/-! Auxiliary cardinal bound for the concrete etale generator.
(blueprint: lem-sc-etale-small-generator-sections-surjective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The section type of the concrete generator is a quotient of a u-small type.
Source: Stacks Project, Tag 01DO, via the affine-model computation and the
u-small affine-open covering argument described in the parent theorem.
(blueprint: lem-sc-etale-small-generator-sections-surjective)

The affine-model construction computes sections as a u-small coproduct of
u-small coefficient groups.  Transport along the small-model equivalences and
restriction to a u-small affine-open covering give a surjection from a type in
`Type u` onto the sections over any etale object.  The empty covering gives the
same conclusion with the singleton domain.
-/
theorem etaleSmallGenerator_sections_surjective (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    ∃ α : Type u, ∃ f : α → ((etaleSmallGenerator X).obj.obj U),
      Function.Surjective f := by
  sorry

end AlgebraicGeometry.Scheme
