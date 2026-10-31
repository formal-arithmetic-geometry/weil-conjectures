/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Complete-intersection local algebras over a field

Source: Stacks Project, Algebra, Definition 10.135.5, Tag 00SD
(blueprint: def-trf-complete-intersection-local).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A local algebra essentially of finite type over a field is a complete intersection
if it is a quotient of an essentially finite type regular local algebra by a finite
regular sequence in its maximal ideal. The empty sequence is allowed.

The presenting algebra lives in `Type (max u v)`: an essentially finite type algebra
is a localization of a finite type algebra, so this universe includes every presentation
up to algebra isomorphism.

Source: Stacks Project, Algebra, Definition 10.135.5, Tag 00SD
(blueprint: def-trf-complete-intersection-local). -/
def IsCompleteIntersectionLocal (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] [EssFiniteType k A] : Prop :=
  ∃ (R : Type (max u v)) (_ : CommRing R) (_ : Algebra k R)
    (_ : IsRegularLocalRing R) (_ : EssFiniteType k R) (xs : List R),
    RingTheory.Sequence.IsRegular R xs ∧
      (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
      Nonempty ((R ⧸ Ideal.ofList xs) ≃ₐ[k] A)

end Algebra
