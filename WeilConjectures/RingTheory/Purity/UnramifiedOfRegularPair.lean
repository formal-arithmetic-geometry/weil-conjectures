/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Support
public import WeilConjectures.RingTheory.Regular.Hartogs

/-!
# Unramifiedness extends across a regular pair

Let `B` be an essentially finite type `A`-algebra and `x, y ∈ A` such that `B` is unramified over
`A` at every prime of `B` not containing `x` and at every prime not containing `y`. If `x` is
`B`-regular and `[x, y]` is weakly regular on `B ⊗[A] B` (e.g. if `B` is flat over `A` and `[x, y]`
is weakly regular on `B`), then `B` is formally unramified over `A`
(`Algebra.FormallyUnramified.of_isWeaklyRegular_tensorProduct`).

Proof. Let `I ⊆ B ⊗[A] B` be the kernel of the multiplication map, a finitely generated ideal with
`I / I² = Ω[B⁄A]`. Since `Ω[B⁄A]` is supported in `V(x)`, some power `x ^ n` maps `I` into `I²`,
and a Nakayama-type determinant trick (`Submodule.exists_sub_pow_mem_and_smul_eq_zero`) gives
`e₁ ∈ I` and `X = x ^ N` with `X i = e₁ i` for `i ∈ I`; similarly `e₂ ∈ I` and `Y = y ^ M`. Then
`Y e₁ = e₁ e₂ = X e₂`, so the regular pair gives `e₁ = X z`; then `z ∈ I` and `z i = i` for
`i ∈ I`, so `I` is idempotent and `Ω[B⁄A] = 0`. (This is the separability idempotent of `B`,
glued from the ones of `B[1/x]` and `B[1/y]`.)

This is step (iii) of the dimension two case of the Zariski–Nagata purity theorem
[Stacks 0BMA], an input of blueprint `sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open RingTheory.Sequence TensorProduct
open scoped Pointwise

namespace Submodule

/-- A variant of **Nakayama's lemma**: if `N` is finitely generated and `c • N ⊆ I • N`, then
there is `r` with `r - c ^ m ∈ I` for some `m` and `r • N = 0`. -/
theorem exists_sub_pow_mem_and_smul_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (c : R)
    (hin : ∀ n ∈ N, c • n ∈ I • N) :
    ∃ r : R, ∃ m : ℕ, r - c ^ m ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have H : ∃ r : R, ∃ m : ℕ, r - c ^ m ∈ I ∧
      N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine ⟨c, 1, by simp, fun n hn ↦ ?_, by rw [← span_le, hs]⟩
    rw [mem_comap, LinearMap.lsmul_apply, hs]
    exact hin n hn
  clear hin hs
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    rcases H with ⟨r, m, hr1, hrn, _⟩
    refine ⟨r, m, hr1, fun n hn ↦ ?_⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  | @insert i s _ _ ih =>
  apply ih
  rcases H with ⟨r, m, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset_iff] at hs
  have : ∃ c' : R, c' - c ^ m ∈ I ∧ c' • i ∈ I • span R s := by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, hdi, rfl⟩
    refine ⟨r - d, ?_, ?_⟩
    · rw [sub_right_comm]
      exact I.sub_mem hr1 hdi
    · rw [sub_smul, ← hyz, add_sub_cancel_left]
      exact hz
  rcases this with ⟨c', hc1, hci⟩
  refine ⟨c' * r, m + m, ?_, ?_, hs.2⟩
  · have : c' * r - c ^ (m + m) = c' * (r - c ^ m) + c ^ m * (c' - c ^ m) := by ring
    rw [this]
    exact I.add_mem (I.mul_mem_left c' hr1) (I.mul_mem_left _ hc1)
  · intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, _, rfl⟩
    simp only [mem_comap, LinearMap.lsmul_apply]
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)

end Submodule

namespace Algebra.FormallyUnramified

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]

/-- If `B` is unramified over `A` at all primes not containing `x`, then some power of `x` maps
the kernel `I` of the multiplication map `B ⊗[A] B → B` into `I²`. -/
theorem exists_pow_mul_mem_ideal_sq (x : A)
    (hx : ∀ (Q : Ideal B) [Q.IsPrime], algebraMap A B x ∉ Q → Algebra.IsUnramifiedAt A Q) :
    ∃ n : ℕ, ∀ i ∈ KaehlerDifferential.ideal A B,
      algebraMap A (B ⊗[A] B) x ^ n * i ∈ KaehlerDifferential.ideal A B ^ 2 := by
  have hrad : algebraMap A B x ∈ (Module.annihilator B Ω[B⁄A]).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hp, hpp⟩
    by_contra hxp
    have hsupp : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B Ω[B⁄A] :=
      Module.mem_support_iff_of_finite.2 hp
    have : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B := hx p hxp
    rw [Algebra.unramifiedLocus_eq_compl_support] at this
    exact this hsupp
  obtain ⟨n, hn⟩ := hrad
  refine ⟨n, fun i hi ↦ ?_⟩
  refine ((KaehlerDifferential.ideal A B).toCotangent_eq_zero
    ⟨_, Ideal.mul_mem_left _ _ hi⟩).1 ?_
  have h1 : KaehlerDifferential.fromIdeal A B ⟨_, Ideal.mul_mem_left _ (algebraMap A _ x ^ n) hi⟩
      = (algebraMap A B x ^ n) • KaehlerDifferential.fromIdeal A B ⟨i, hi⟩ := by
    have : (⟨_, Ideal.mul_mem_left _ (algebraMap A _ x ^ n) hi⟩ : KaehlerDifferential.ideal A B)
        = (algebraMap A (B ⊗[A] B) x ^ n) • ⟨i, hi⟩ := rfl
    rw [this, map_smul, ← map_pow, ← map_pow, algebraMap_smul, algebraMap_smul]
  exact h1.trans (Module.mem_annihilator.1 hn _)

end Algebra.FormallyUnramified

/-- See the module docstring. -/
theorem Algebra.FormallyUnramified.of_isWeaklyRegular_tensorProduct {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B] {x y : A}
    (hreg : IsWeaklyRegular (R := A) (B ⊗[A] B) [x, y]) (hxB : IsSMulRegular B x)
    (hx : ∀ (Q : Ideal B) [Q.IsPrime], algebraMap A B x ∉ Q → Algebra.IsUnramifiedAt A Q)
    (hy : ∀ (Q : Ideal B) [Q.IsPrime], algebraMap A B y ∉ Q → Algebra.IsUnramifiedAt A Q) :
    Algebra.FormallyUnramified A B := by
  set F := B ⊗[A] B
  set I := KaehlerDifferential.ideal A B
  have hfg : I.FG := KaehlerDifferential.ideal_fg A B
  -- the determinant trick for `x` and for `y`
  have key : ∀ t : A, (∀ (Q : Ideal B) [Q.IsPrime], algebraMap A B t ∉ Q →
      Algebra.IsUnramifiedAt A Q) → ∃ N : ℕ, ∃ e ∈ I, ∀ i ∈ I,
        algebraMap A F t ^ N * i = e * i := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_ideal_sq t ht
    obtain ⟨r, m, hr, hr0⟩ := Submodule.exists_sub_pow_mem_and_smul_eq_zero I I hfg
      (algebraMap A F t ^ n) fun i hi ↦ by
        rw [smul_eq_mul, ← pow_two]
        exact hn i hi
    refine ⟨n * m, -(r - (algebraMap A F t ^ n) ^ m), I.neg_mem hr, fun i hi ↦ ?_⟩
    have := hr0 i hi
    rw [smul_eq_mul] at this
    rw [pow_mul]
    linear_combination this
  obtain ⟨N, e₁, he₁, h₁⟩ := key x hx
  obtain ⟨M, e₂, he₂, h₂⟩ := key y hy
  obtain ⟨hxF, hyF⟩ := IsWeaklyRegular.isSMulRegular_and_mem_smul_top hreg
  -- `y ^ M e₁ = e₁ e₂ = x ^ N e₂`
  have h12 : y ^ M • e₁ = x ^ N • e₂ := by
    rw [Algebra.smul_def, Algebra.smul_def, map_pow, map_pow, h₂ e₁ he₁, h₁ e₂ he₂, mul_comm]
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (mem_pow_smul_top_of_pow_smul_mem hxF hyF N M
      (by rw [h12]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top))
  -- `z ∈ I`
  have hzI : z ∈ I := by
    change TensorProduct.lmul' A z = 0
    refine (hxB.pow N) ?_
    beta_reduce
    rw [smul_zero, ← map_smul, hz]
    exact he₁
  -- `z i = i` for `i ∈ I`
  have hzi : ∀ i ∈ I, z * i = i := by
    intro i hi
    refine (hxF.pow N) ?_
    beta_reduce
    rw [← smul_mul_assoc, hz, Algebra.smul_def, map_pow, h₁ i hi]
  have hidem : IsIdempotentElem I := by
    refine le_antisymm Ideal.mul_le_left fun i hi ↦ ?_
    rw [← hzi i hi]
    exact Ideal.mul_mem_mul hzI hi
  exact ⟨(Ideal.cotangent_subsingleton_iff I).2 hidem⟩
