/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
import WeilConjectures.RingTheory.StrictHenselizationQuotientBases
import WeilConjectures.RingTheory.FixedQuotientBasesCompletion

/-!
# Fixed bases for strict henselization quotients and their completed comparison

For a strict henselization `C` of a Noetherian local ring `A` with maximal ideal `n`, there
are fixed elements of `C` whose classes form bases of every quotient `C ⧸ (nC)^r` over
`A ⧸ n^r`, and the induced compatible isomorphisms identify the `nC`-adic completion of `C`
with the `n`-adic completion of the free `A`-module on these elements.

## Implementation details

The quotient isomorphisms are written as `A`-linear equivalences. Both sides are annihilated
by the same power of the maximal ideal, so this is exactly linearity over `A ⧸ n^r`. The
completed comparison is the canonical inverse-limit comparison induced by the quotient bases,
characterized by its value at each positive-power coordinate.

## References

* [Stacks, Tag 07QM], part (4)
* [Stacks, Tag 06LJ], proof of (c)
-/

@[expose] public section

universe u

namespace Algebra

/-- There are fixed lifts in the strict henselization giving bases of every positive-power
quotient, and the induced compatible quotient isomorphisms identify its ring completion
with the module completion of the free module on those lifts. -/
theorem strictHenselization_mod_power_free
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (X : Type u) (x : X → C)
      (e : ∀ (r : ℕ), 1 ≤ r →
        (X →₀ A ⧸ (IsLocalRing.maximalIdeal A) ^ r) ≃ₗ[A]
          C ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r),
      (∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
        e r hr (Finsupp.single i 1) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r)
            (x i)) ∧
      ∃ E : AdicCompletion (IsLocalRing.maximalIdeal A) (X →₀ A) ≃ₗ[A]
          AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C,
        ∀ (r : ℕ) (hr : 1 ≤ r)
          (z : AdicCompletion (IsLocalRing.maximalIdeal A) (X →₀ A)) (f : X →₀ A),
          AdicCompletion.eval (IsLocalRing.maximalIdeal A) (X →₀ A) r z =
            ((IsLocalRing.maximalIdeal A) ^ r •
              (⊤ : Submodule A (X →₀ A))).mkQ f →
          AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) r
              (E z) =
            e r hr (f.mapRange (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ r))
              (map_zero (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ r)))) := by
  obtain ⟨X, x, e, he⟩ := strictHenselization_quotient_bases A K C hC
  refine ⟨X, x, e, he, ?_⟩
  exact AdicCompletion.equiv_of_fixed_quotient_bases
    (IsLocalRing.maximalIdeal A) X x e he

end Algebra
