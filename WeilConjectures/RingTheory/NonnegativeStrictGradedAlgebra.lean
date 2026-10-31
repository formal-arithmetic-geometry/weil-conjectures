/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Nonnegative strictly graded commutative algebras

Source: Stacks Project, Tag 09PF, the grading conventions preceding Tag 09PG, and
Tag 09PG, the observation following the definition of divided powers.
(blueprint: def-sfb-nonnegative-strict-graded-algebra)

The underlying nonnegative grading is Mathlib's `GradedAlgebra`. The parity parts
are submodules of the original algebra, formed by sums of the indicated components.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedAlgebra

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- Strict graded commutativity imposes both the Koszul sign rule and vanishing
of odd homogeneous squares, including in characteristic two.
Source: Stacks Project, Tag 09PF, immediately before Tag 09PG.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
class IsStrictlyGradedCommutative (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : Prop where
  /-- Homogeneous elements commute with the Koszul sign. -/
  signed_comm : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
    x * y = (-1 : A) ^ (i * j) * (y * x)
  /-- Every odd homogeneous element has zero square. -/
  odd_sq_zero : ∀ (i : ℕ) (x : A), Odd i → x ∈ 𝒜 i → x ^ 2 = 0

/-- Extend a nonnegative grading by zero in negative integer degrees.
Source: Stacks Project, Tag 09PF, nonnegative grading convention.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def integerComponent (𝒜 : ℕ → Submodule R A) : ℤ → Submodule R A
  | .ofNat n => 𝒜 n
  | .negSucc _ => ⊥

/-- The even part inside the original algebra: finite sums of even components.
Source: Stacks Project, Tag 09PF, immediately before Tag 09PG.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def evenPart (𝒜 : ℕ → Submodule R A) : Submodule R A :=
  ⨆ i : ℕ, 𝒜 (2 * i)

/-- The odd part inside the original algebra: finite sums of odd components.
Source: Stacks Project, Tag 09PF, immediately before Tag 09PG.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def oddPart (𝒜 : ℕ → Submodule R A) : Submodule R A :=
  ⨆ i : ℕ, 𝒜 (2 * i + 1)

/-- The positive even part inside the original algebra; degree zero is excluded.
Source: Stacks Project, Tag 09PG, the positive even ideal.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def positiveEvenPart (𝒜 : ℕ → Submodule R A) : Submodule R A :=
  ⨆ i : ℕ, ⨆ (_ : 0 < i), 𝒜 (2 * i)

/-- The even part contains the unit, is multiplicatively closed and commutative,
and multiplication by an even element preserves the positive even part.
Source: Stacks Project, Tags 09PF and 09PG, observation after the definition.
(blueprint: def-sfb-nonnegative-strict-graded-algebra).

Proof: The internal direct-sum grading identifies the displayed submodule sums
with the images of the restricted direct sums: every element is a finite sum
of homogeneous components, and injectivity is inherited from the full sum map.
The unit is in degree zero by `def-sfb-nonnegative-graded-algebra`, hence in the
even part. Products of degrees 2i and 2j have degree 2(i+j), so distributivity
and induction on finite sums give multiplicative closure. The sign in the
homogeneous commutation rule is one for these even degrees; expanding finite
sums gives commutativity. If j is positive, i+j is positive, so the same finite
expansion proves stability of the positive even part under even multiplication.
The submodule axioms already give addition, negation and scalar closure, and
the scalar image belongs to degree zero because r = r • 1. -/
theorem parity_properties (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] :
    (1 : A) ∈ evenPart 𝒜 ∧
    (∀ (x y : A), x ∈ evenPart 𝒜 → y ∈ evenPart 𝒜 → x * y ∈ evenPart 𝒜) ∧
    (∀ (x y : A), x ∈ evenPart 𝒜 → y ∈ evenPart 𝒜 → x * y = y * x) ∧
    (∀ (x y : A), x ∈ evenPart 𝒜 → y ∈ positiveEvenPart 𝒜 →
      x * y ∈ positiveEvenPart 𝒜) := by
  sorry

/-- The even subalgebra, with its actual inherited operations and carrier.
Source: Stacks Project, Tags 09PF and 09PG.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def evenSubalgebra (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] : Subalgebra R A :=
  (evenPart 𝒜).toSubalgebra (parity_properties 𝒜).1 (parity_properties 𝒜).2.1

/-- The inherited ring structure on the even subalgebra is commutative.
Source: Stacks Project, Tag 09PG, observation after the definition.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
instance evenSubalgebraCommRing (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] : CommRing (evenSubalgebra 𝒜) :=
  { (inferInstance : Ring (evenSubalgebra 𝒜)) with
    mul_comm := fun x y ↦ Subtype.ext ((parity_properties 𝒜).2.2.1 x y x.prop y.prop) }

/-- The positive even ideal in the even subalgebra, with membership inherited
from the positive even submodule of the original algebra.
Source: Stacks Project, Tag 09PG, observation after the definition.
(blueprint: def-sfb-nonnegative-strict-graded-algebra). -/
def positiveEvenIdeal (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] : Ideal (evenSubalgebra 𝒜) where
  carrier := {x | (x : A) ∈ positiveEvenPart 𝒜}
  zero_mem' := (positiveEvenPart 𝒜).zero_mem
  add_mem' := fun hx hy ↦ (positiveEvenPart 𝒜).add_mem hx hy
  smul_mem' := fun x y hy ↦ (parity_properties 𝒜).2.2.2 x y x.prop hy

end GradedAlgebra
