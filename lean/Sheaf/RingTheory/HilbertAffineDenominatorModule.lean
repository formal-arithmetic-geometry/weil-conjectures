/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Affine denominator maps on a finite module

Source: Stacks Project, Divisors, Tag 02P2, Lemma 31.25.5, affine proof
(blueprint: lem-sc-hilbert-affine-denominator-module).
-/

@[expose] public section

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
  classical
  have _hSupport := hSupport
  let Q := Localization (nonZeroDivisors A)
  let s : Q := IsLocalization.mk' Q a ⟨b, hb⟩
  have hreg (c : A) (hc : c ∈ nonZeroDivisors A) : IsSMulRegular M c := by
    by_contra h
    have hc' : c ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact h
    obtain ⟨p, hp, hcp⟩ := Set.mem_iUnion₂.mp hc'
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hcp (hAssoc hp) hc
  have haM := hreg a ha
  have hbM := hreg b hb
  have hinjQ : Function.Injective (algebraMap A Q) :=
    IsLocalization.injective Q le_rfl
  have hfrac (c x : A) :
      algebraMap A Q c = s * algebraMap A Q x ↔ b * c = a * x := by
    have hs : algebraMap A Q b * s = algebraMap A Q a :=
      IsLocalization.mk'_spec' Q a ⟨b, hb⟩
    constructor
    · intro h
      apply hinjQ
      rw [map_mul, h, ← mul_assoc, hs, ← map_mul]
    · intro h
      apply (IsUnit.mul_right_inj (IsLocalization.map_units Q ⟨b, hb⟩)).mp
      change algebraMap A Q b * algebraMap A Q c =
        algebraMap A Q b * (s * algebraMap A Q x)
      rw [← mul_assoc, hs, ← map_mul, ← map_mul, h]
  let B : M →ₗ[A] M := LinearMap.lsmul A M b
  -- Describe the denominator ideals by clearing the regular denominator.
  let I : Ideal A :=
    (LinearMap.range (LinearMap.mulLeft A b)).comap (LinearMap.mulLeft A a)
  let J : Ideal A :=
    (LinearMap.range (LinearMap.mulLeft A a)).comap (LinearMap.mulLeft A b)
  have hI (x : A) : x ∈ I ↔ ∃ c : A, b * c = a * x := Iff.rfl
  have hJ (c : A) : c ∈ J ↔ ∃ x ∈ I, b * c = a * x := by
    change (∃ x : A, a * x = b * c) ↔ _
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (hI x).mpr ⟨c, hx.symm⟩, hx.symm⟩
    · rintro ⟨x, _, hx⟩
      exact ⟨x, hx.symm⟩
  refine ⟨I, J, ?_, IsNoetherian.noetherian I, ?_, hbM, ?_, ?_⟩
  · intro x
    change x ∈ I ↔ ∃ c : A, algebraMap A Q c = s * algebraMap A Q x
    simp only [hfrac, hI]
  · intro c
    change c ∈ J ↔ ∃ x ∈ I, algebraMap A Q c = s * algebraMap A Q x
    simp only [hfrac, hJ]
  · apply (IsLocalizedModule.injective_iff_isRegular (Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers b) M)).mpr
    rintro ⟨c, hc⟩
    obtain ⟨n, rfl⟩ := hc
    exact hbM.pow n
  let N : Submodule A M := I • (⊤ : Submodule A M)
  have hN (z : N) : a • (z : M) ∈ LinearMap.range B := by
    have hz := z.property
    change (z : M) ∈ I • (⊤ : Submodule A M) at hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro x hx m _
      obtain ⟨c, hc⟩ := (hI x).mp hx
      refine ⟨c • m, ?_⟩
      change b • (c • m) = a • (x • m)
      simp only [← mul_smul, hc]
    · intro x y hx hy
      simpa only [smul_add] using (LinearMap.range B).add_mem hx hy
  let g : N →ₗ[A] M := (LinearMap.lsmul A M a).comp N.subtype
  -- Multiplication by b identifies M with its range, giving the unique division map.
  let f : N →ₗ[A] M := g.codRestrictOfInjective B hbM hN
  have hf (z : N) : b • f z = a • (z : M) :=
    LinearMap.codRestrictOfInjective_comp_apply g B hbM hN z
  refine ⟨N.injective_subtype, f, hf, ?_, ?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply haM
    change a • (x : M) = a • (y : M)
    rw [← hf, ← hf, h]
  · rw [Submodule.annihilator_quotient]
    intro i hi
    rw [Submodule.mem_colon]
    intro m _
    exact ⟨⟨i • m, Submodule.smul_mem_smul hi (Submodule.mem_top)⟩, rfl⟩
  · rw [Submodule.annihilator_quotient]
    intro c hc
    rw [Submodule.mem_colon]
    intro m _
    obtain ⟨x, hx, hcx⟩ := (hJ c).mp hc
    refine ⟨⟨x • m, Submodule.smul_mem_smul hx (Submodule.mem_top)⟩, ?_⟩
    apply hbM
    change b • f ⟨x • m, _⟩ = b • (c • m)
    rw [hf]
    change a • (x • m) = b • (c • m)
    simp only [← mul_smul, hcx]

end Module
