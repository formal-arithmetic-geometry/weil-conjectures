module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Divided powers on a split square-zero extension

Source: Stacks Project, `dpa.tex`, Tags 09PH and 07GL; the ordinary even-ring
calculation underlying adjoining an odd variable.
(blueprint: lem-sfb-split-square-zero-divided-powers)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace DividedPowers.SplitSquareZero

/-- The canonical right action induced by the given left action over a commutative ring.
Source: Stacks, Tag 09PH, the multiplication on the split extension.
(blueprint: lem-sfb-split-square-zero-divided-powers) -/
abbrev rightModule (C : Type u) [CommRing C] (M : Type v)
    [AddCommGroup M] [Module C M] : Module Cᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id C).fromOpposite (fun a b ↦ mul_comm a b))

attribute [local instance] rightModule

/-- The canonical right and left actions agree, so the split extension is commutative.
Source: Stacks, Tag 09PH, the ordinary even-ring calculation.
(blueprint: lem-sfb-split-square-zero-divided-powers) -/
abbrev centralScalar (C : Type u) [CommRing C] (M : Type v)
    [AddCommGroup M] [Module C M] : IsCentralScalar C M :=
  ⟨fun _ _ ↦ rfl⟩

attribute [local instance] centralScalar

/-- The divided powers on `I ⊕ M` extending those on `I` and trivial in degrees above one
on `M` exist uniquely and have the first-order formula.
Source: Stacks, Tags 09PH (displayed extension formula) and 07GL (ordinary axioms).
(blueprint: lem-sfb-split-square-zero-divided-powers)

Proof: Use the standard split multiplication (c,u)(d,v) = (cd,cv+du).
The inverse image of I under the first projection is exactly I ⊕ M and is an ideal.
Set delta_0 = (1,0), and delta_n(x,u) = (gamma_n(x),gamma_(n-1)(x) • u)
for n positive, extending by zero outside the ideal. Positive divided powers of zero
vanish by the scalar axiom. The product axiom gives x gamma_(r-1)(x) = r gamma_r(x),
including r = 1 by gamma_0 = 1. Thus delta_1 is the identity and the two restrictions
hold. For the scalar axiom with an arbitrary scalar (c,v), use
(c,v)^n = (c^n,n c^(n-1) • v); the second components agree by the displayed identity.
For addition the first component is the addition axiom for gamma. In the second
component, shift the index in the coefficient of u and in that of v; each sum is
exactly gamma_(n-1)(x+y). For multiplication the coefficient of u is
(gamma_n(x) gamma_(m-1)(x) + gamma_(n-1)(x) gamma_m(x)); the product axiom and
Pascal's identity make it choose(n+m,n) gamma_(n+m-1)(x).
For iteration put q(n,m) = (nm)!/(n!(m!)^n), an integer. The case n = 1 is immediate.
For n at least two, the iteration and product axioms for gamma give second component
q(n-1,m) choose(nm-1,m-1) gamma_(nm-1)(x) • u. The integer coefficient equals q(n,m)
by the factorial identity; this identity is checked in the integers, without division
in C. The first component is the iteration axiom for gamma. This proves all five
axioms. Finally, any competing structure has fixed degrees zero and one. Apply its
addition axiom to (x,0)+(0,u) in higher degrees: only degrees zero and one on (0,u)
survive, forcing the same formula and hence equality of all operations. -/
theorem exists_unique (C : Type u) [CommRing C] (I : Ideal C) (γ : DividedPowers I)
    (M : Type v) [AddCommGroup M] [Module C M] :
    ∃ δ : DividedPowers (I.comap (TrivSqZeroExt.fstHom C C M).toRingHom),
      (∀ (n : ℕ) (x : C), x ∈ I →
        δ.dpow n (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl (γ.dpow n x)) ∧
      (∀ (n : ℕ) (u : M), 1 < n → δ.dpow n (TrivSqZeroExt.inr u) = 0) ∧
      (∀ (n : ℕ) (x : C) (u : M), 0 < n → x ∈ I →
        δ.dpow n (TrivSqZeroExt.inl x + TrivSqZeroExt.inr u) =
          TrivSqZeroExt.inl (γ.dpow n x) + TrivSqZeroExt.inr (γ.dpow (n - 1) x • u)) ∧
      ∀ η : DividedPowers (I.comap (TrivSqZeroExt.fstHom C C M).toRingHom),
        (∀ (n : ℕ) (x : C), x ∈ I →
          η.dpow n (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl (γ.dpow n x)) →
        (∀ (n : ℕ) (u : M), 1 < n → η.dpow n (TrivSqZeroExt.inr u) = 0) → η = δ := by
  sorry

end DividedPowers.SplitSquareZero
