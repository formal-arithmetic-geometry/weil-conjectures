/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Affine denominator maps on a finite module

Source: Stacks Project, Divisors, Tag 02P2, Lemma 31.25.5, affine proof
(blueprint: lem-sc-hilbert-affine-denominator-module).
-/

universe u v

namespace Module

/-- The affine denominator calculation of Stacks Project, Tag 02P2
(blueprint: lem-sc-hilbert-affine-denominator-module).
The ideals `I` and `J` are characterized inside the total quotient ring by
`I = {x | sx ∈ A}` and `J = sI`, where `s = a/b`. The domain is the actual
submodule `I • ⊤`, not the tensor product `I ⊗ M`. The first map is its inclusion.
The second is uniquely characterized by `b • f(z) = a • z`, because `b` acts
injectively on `M`; this is equivalent to the rule `f(z)/1 = az/b` in `M_b`.

Proof: (1) The set of denominators is closed under addition and multiplication
by `A`; it is an ideal, finitely generated since `A` is Noetherian.
(2) A ring nonzerodivisor avoids every minimal prime by
`lem-pc-minimal-prime-avoids-nonzerodivisor`, and hence every associated prime
of `M`. By `lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`,
both `a` and `b` act injectively on `M`. Thus `M → M_b` is injective.
(3) For each generator `x • m` of `IM`, the scalar `sx` is in `A`; multiplication
by `s` therefore lands in `M` and defines `f`. It is injective since `a` acts
injectively. The inclusion of `IM` is also injective.
(4) Every `i ∈ I` sends `M` into `IM`, so it kills the first cokernel.
(5) Every `c = si ∈ J` sends `m` to `f(i • m)`, so it kills the second cokernel. -/
theorem hilbert_affine_denominator_module
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hSupport : Module.support A M = Set.univ)
    (hAssoc : associatedPrimes A M ⊆ minimalPrimes A)
    (a b : A) (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A) :
    let Q := Localization (nonZeroDivisors A)
    let s : Q := IsLocalization.mk' Q a ⟨b, hb⟩
    ∃ (I J : Ideal A),
      (∀ x : A, x ∈ I ↔ ∃ c : A, algebraMap A Q c = s * algebraMap A Q x) ∧
      I.FG ∧
      (∀ c : A, c ∈ J ↔ ∃ x ∈ I, algebraMap A Q c = s * algebraMap A Q x) ∧
      IsSMulRegular M b ∧
      Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers b) M) ∧
      let N : Submodule A M := I • (⊤ : Submodule A M)
      Function.Injective N.subtype ∧
      ∃ f : N →ₗ[A] M,
        (∀ z : N, b • f z = a • (z : M)) ∧
        Function.Injective f ∧
        I ≤ Module.annihilator A (M ⧸ LinearMap.range N.subtype) ∧
        J ≤ Module.annihilator A (M ⧸ LinearMap.range f) := by
  sorry

end Module
