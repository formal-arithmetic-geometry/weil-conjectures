/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Functorial injective embeddings for group-ring modules

Source: Stacks Project, Injectives, Section G-modules, paragraph before Tag 04JF
(blueprint: lem-exc-rg-group-algebra-functorial-injective-embeddings).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- For a group `G` and a ring `R`, left modules over `R[G]` admit a functorial
monomorphism into injective modules (Stacks, Injectives, Section G-modules,
paragraph before Tag 04JF) (blueprint: lem-exc-rg-group-algebra-functorial-injective-embeddings).

Proof: The group ring `R[G]` is a ring. Its module category is Grothendieck
abelian by the module-category theorem
`lem-weil-pbc-ring-modules-grothendieck-abelian`. Apply
`lem-weil-pbc-grothendieck-functorial-injective-embedding` to this category.
The resulting functor and natural transformation have monic components and
injective values. -/
theorem groupAlgebra_functorialInjectiveEmbeddings
    {G : Type v} [Group G] (R : Type u) [Ring R] :
    ∃ (J : ModuleCat.{max u v} (MonoidAlgebra R G) ⥤
        ModuleCat.{max u v} (MonoidAlgebra R G)) (j : 𝟭 _ ⟶ J),
      (∀ M, Mono (j.app M)) ∧ ∀ M, Injective (J.obj M) := by
  sorry

end ModuleCat
