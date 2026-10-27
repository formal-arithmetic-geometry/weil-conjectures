module

public import Sheaf.RingTheory.NonnegativeStrictGradedAlgebra
public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Divided powers on a strictly graded commutative algebra

Source: Stacks Project, Tag 09PG, Definition `definition-divided-powers-graded` and
its following observation (blueprint: def-sfb-graded-divided-power-structure).

The ordinary axioms are Mathlib's `DividedPowers` on the positive even ideal of the
commutative even subalgebra. The two additional axioms express compatibility with
the grading and vanishing on homogeneous odd products. There is no differential.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedAlgebra

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A graded divided-power structure on a nonnegative strictly graded commutative algebra.
Source: Stacks Project, Tag 09PG, all seven axioms and the following observation
(blueprint: def-sfb-graded-divided-power-structure).

The inherited ordinary divided powers give the positive operations, their ideal-valuedness,
the convention `γ₀ = 1`, identity, multiplication, even-scalar, addition and composition axioms.
Their values outside the positive even ideal are fixed to zero, as in Mathlib's encoding;
this adds no data or condition on the operations on the ideal. The composition coefficient
`Nat.uniformBell n m` is the integer `(n*m)! / (n! * (m!)^n)`, as expressed by
`Nat.uniformBell_mul_eq`; all coefficients act by their natural-number casts.
In the odd-product axiom, `z` names the even element whose underlying value is the product;
such a product has positive even degree by the grading. No axiom is imposed on sums of
odd products beyond the ordinary divided-power addition axiom. -/
structure GradedDividedPowers (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] extends DividedPowers (positiveEvenIdeal 𝒜) where
  /-- Positive divided powers multiply the homogeneous degree by their index. -/
  dpow_homogeneous : ∀ (n i : ℕ) (x : evenSubalgebra 𝒜),
    0 < n → 0 < i → (x : A) ∈ 𝒜 (2 * i) →
      (dpow n x : A) ∈ 𝒜 (2 * i * n)
  /-- Higher divided powers vanish on each product of two homogeneous odd elements. -/
  dpow_odd_mul : ∀ (n i j : ℕ) (x y : A) (z : evenSubalgebra 𝒜),
    1 < n → x ∈ 𝒜 (2 * i + 1) → y ∈ 𝒜 (2 * j + 1) →
      (z : A) = x * y → dpow n z = 0

end GradedAlgebra
