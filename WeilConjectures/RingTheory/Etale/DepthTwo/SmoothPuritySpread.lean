/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityStep
public import WeilConjectures.RingTheory.Etale.IntegralClosureSpreading

/-!
# Spreading out finite étaleness of a normal cover of a smooth algebra

Let `R₀` be a Noetherian integrally closed domain, `B` a smooth `R₀`-algebra, `M` a `B`-algebra in
which the nonzero elements of `R₀` are invertible and `T` the integral closure of `B` in `M`. Let
`P` be a prime of `B` not over `0`, such that `T` is finite étale over a neighbourhood of every
prime `Q ⊊ P`. If `B_P ⊗_B T` is finite étale over `B_P`, then `T` is finite étale over a
neighbourhood `D(h)` of `P` (`RingTheory.DepthTwo.exists_etale_finite_away_of_localization`).

Proof. Shrinking, `B_h` is a normal domain, and every prime of `D(h)` over `0 ⊆ R₀` has a
neighbourhood over which `T` is finite étale (the locus where `T` is finite étale is open and
contains all strict generizations of `P`). Then `B_h ⊗ T` is torsion free, so it embeds into
`K ⊗ T` (`K = Frac B`), an étale `K`-algebra, and `B_h ⊗ T` is finite as it lies in the integral
closure of `B_h` (`RingTheory.DepthTwo.finite_integralClosure_of_etale`). Finally étaleness
spreads out from `B_P` (`Algebra.exists_etale_away_tensor_of_isLocalization`).

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace Algebra

/-- **Spreading out étaleness from a localization of the base.** If `X` is a finitely presented
`A`-algebra and `S⁻¹A ⊗_A X` is étale over `S⁻¹A`, then `A_s ⊗_A X` is étale over `A_s` for some
`s ∈ S`. -/
theorem exists_etale_away_tensor_of_isLocalization {A A' X : Type u} [CommRing A] [CommRing A']
    [CommRing X] [Algebra A A'] [Algebra A X] [Algebra.FinitePresentation A X]
    (S : Submonoid A) [IsLocalization S A'] [Algebra.Etale A' (A' ⊗[A] X)] :
    ∃ s ∈ S, Algebra.Etale (Localization.Away s) (Localization.Away s ⊗[A] X) := by
  let : Algebra X (A' ⊗[A] X) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid X S) (A' ⊗[A] X) :=
    IsLocalization.tensorRight _ _
  have : IsScalarTower A X (A' ⊗[A] X) := .of_algebraMap_eq fun b ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have : Algebra.FormallyEtale A A' := .of_isLocalization S
  have : Algebra.FormallyEtale A (A' ⊗[A] X) := .comp A A' _
  obtain ⟨_, ⟨s, hs, rfl⟩, hEt⟩ := Algebra.exists_etale_localizationAway_of_isLocalization
    (B := A) (L := A' ⊗[A] X) (Algebra.algebraMapSubmonoid X S)
  refine ⟨s, hs, ?_⟩
  let Y := Localization.Away s ⊗[A] X
  let : Algebra X Y := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization.Away (algebraMap A X s) Y :=
    IsLocalization.Away.tensorRight s (Localization.Away s)
  have : IsScalarTower A X Y := .of_algebraMap_eq fun b ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  let e : Y ≃ₐ[X] Localization.Away (algebraMap A X s) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap A X s)) Y _
  have : Algebra.Etale A Y := .of_equiv (e.symm.restrictScalars A)
  exact Algebra.Etale.of_restrictScalars A (Localization.Away s) Y

end Algebra

namespace RingTheory.DepthTwo

section Locus

variable {B : Type*} [CommRing B] [IsNoetherianRing B]

/-- **Avoiding the bad locus.** Let `good` be a property of elements of a Noetherian ring `B`,
and `P` a prime such that every prime `Q ⊊ P` avoids some `good` element. Then there is `h₀ ∉ P`
such that every prime `Q ∌ h₀` not containing `P` avoids some `good` element: the closed set of
primes containing all `good` elements meets `D(h₀)` inside `V(P)`. -/
lemma exists_forall_exists_not_mem (good : B → Prop) (P : Ideal B) [P.IsPrime]
    (H : ∀ Q : Ideal B, Q.IsPrime → Q < P → ∃ h ∉ Q, good h) :
    ∃ h₀ ∉ P, ∀ Q : Ideal B, Q.IsPrime → h₀ ∉ Q → ¬ P ≤ Q → ∃ h ∉ Q, good h := by
  classical
  let I := Ideal.span {h | good h}
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  let s := hfin.toFinset.filter fun p ↦ ¬ p ≤ P
  have hs (p : Ideal B) (hp : p ∈ s) : ∃ x ∈ p, x ∉ P := Set.not_subset.1 (Finset.mem_filter.1 hp).2
  choose! f hf using hs
  refine ⟨∏ p ∈ s, f p, ?_, fun Q hQ hQh hPQ ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hfp⟩
    exact (hf p hp).2 hfp
  · by_contra! hall
    obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := Q)
      (Ideal.span_le.2 fun h hh ↦ by_contra fun hhQ ↦ hall h hhQ hh)
    have := hp.1.1
    by_cases hpP : p ≤ P
    · rcases lt_or_eq_of_le hpP with hlt | rfl
      · obtain ⟨h, hhp, hh⟩ := H p this hlt
        exact hhp (hp.1.2 (Ideal.subset_span hh))
      · exact hPQ hpQ
    · have hps : p ∈ s := Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hp, hpP⟩
      exact hQh ((Ideal.IsPrime.prod_mem_iff).2 ⟨p, hps, hpQ (hf p hps).1⟩)

end Locus

end RingTheory.DepthTwo
