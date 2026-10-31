/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Complete-intersection local algebras over a field

Source: Stacks Project, Algebra, Tag 00SD (definition-lci-local-ring)
(blueprint: def-trf-complete-intersection-local-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A complete-intersection local algebra is a local algebra essentially of finite type
which is a quotient of a regular local algebra essentially of finite type by a finite
regular sequence in its maximal ideal. The empty sequence is allowed. The presenting
ring lives in the maximum of the coefficient and target universes; an essentially finite
type algebra has such a representative, being a localization of a finite type algebra.
Source: Stacks Project, Algebra, Tag 00SD (definition-lci-local-ring)
(blueprint: def-trf-complete-intersection-local-algebra). -/
def IsCompleteIntersectionLocalAlgebra (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] : Prop :=
  IsLocalRing A ∧ EssFiniteType k A ∧
    ∃ (R : Type (max u v)) (_ : CommRing R) (_ : Algebra k R)
      (_ : IsRegularLocalRing R),
      EssFiniteType k R ∧ ∃ xs : List R,
        RingTheory.Sequence.IsRegular R xs ∧
          (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
          Nonempty ((R ⧸ Ideal.ofList xs) ≃ₐ[k] A)

end Algebra
