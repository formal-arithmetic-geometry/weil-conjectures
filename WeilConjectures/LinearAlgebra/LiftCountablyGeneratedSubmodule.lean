/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Data.Set.Countable

/-!
# Lifting a countably generated submodule through scalar extension

Source: Stacks Project, Algebra, Tag 05A7, `lemma-lift-countably-generated-submodule`.
(blueprint: lem-trf-lift-countably-generated-submodule).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Submodule

/-- A countably generated submodule of a scalar extension is contained in the
base change of a countably generated submodule downstairs.

Source: Stacks Project, Algebra, Tag 05A7, `lemma-lift-countably-generated-submodule`.
(blueprint: lem-trf-lift-countably-generated-submodule).

Proof: Choose a countable spanning set for `Q`. Each of its elements is a finite
sum of pure tensors, so the union of all second factors in those sums is
countable. Let `P` be the `A`-span of these factors. The universal property of
the tensor product gives the natural `B`-linear map from `B ⊗[A] P` to
`B ⊗[A] L`, and each chosen generator of `Q` lies in its range. Hence all of
`Q` lies in the base change `P.baseChange B`. Empty and finite generating sets
are allowed, and no injectivity or flatness is used.
-/
theorem exists_countable_submodule_lift
    {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
    {L : Type w} [AddCommGroup L] [Module A L]
    (Q : Submodule B (B ⊗[A] L))
    (hQ : ∃ s : Set (B ⊗[A] L), s.Countable ∧ Submodule.span B s = Q) :
    ∃ P : Submodule A L,
      (∃ s : Set L, s.Countable ∧ Submodule.span A s = P) ∧
      Q ≤ P.baseChange B := by
  sorry

end Submodule
