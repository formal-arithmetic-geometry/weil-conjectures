module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Positive powers preserve a finite scalar family's zero common kernel

Source: Stacks Project, Algebra, Tag 0565 (lemma-when-injective-covering), converse proof.
(blueprint: lem-trf-finite-scalar-power-common-kernel)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- If the scalar-coordinate map into a finite direct sum is injective, positive powers
of those scalars still have zero common kernel.

Source: Stacks Project, Algebra, Tag 0565 (lemma-when-injective-covering), converse proof.
(blueprint: lem-trf-finite-scalar-power-common-kernel)

Proof plan: Injectivity says that if every `f i` kills an element, that element is zero.
For `n = 0`, the direct sum has only the empty tuple, so injectivity forces `M = 0`.
For positive `n`, strongly induct on the sum of the excess exponents `e i - 1`,
uniformly in the module element. If the sum is zero, every exponent is one, and
injectivity gives the result. Otherwise choose `k` with `e k > 1` and apply induction
to `f k • m`, decreasing just the kth exponent by one. Associativity gives its kth
annihilation equation; commutativity of `A` gives all the other equations. Thus
`f k • m = 0`. Replace the kth exponent by one and apply induction again to `m`.
This second tuple has smaller excess sum and all its power-annihilation equations hold,
so `m = 0`. The direct sum and its components are those of
`def-weil-pbc-direct-sum-modules`, implemented by Mathlib's `DirectSum` API. -/
theorem finite_scalar_power_common_kernel
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (f : Fin n → A)
    (hinj : Function.Injective (fun m : M ↦
      (DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ ↦ M)).symm
        (fun i ↦ f i • m)))
    (e : Fin n → ℕ) (he : ∀ i, 1 ≤ e i) (m : M)
    (hm : ∀ i, f i ^ e i • m = 0) : m = 0 := by
  sorry

end Module
