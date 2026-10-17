/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurity
public import WeilConjectures.RingTheory.Etale.DepthTwo.Rank
public import WeilConjectures.RingTheory.Etale.DepthTwo.LocalToGlobal

/-!
# Purity over a discrete valuation ring

Let `R₀` be a discrete valuation ring, `B` a smooth `R₀`-algebra, `B_K` the localization of `B`
at the nonzero elements of `R₀` and `L` a finite étale `B_K`-algebra, with integral closure `T₀`
of `B` in `L`. If `T₀` is finite étale over `B` at the generic points of the closed fibre (the
minimal primes of `𝔪 B`), then `D ⊗[B] T₀` is finite étale over `D` for every `B`-algebra `D`
(`RingTheory.DepthTwo.etale_finite_tensor_integralClosure_of_minimalPrimes`).

Away from the closed fibre `T₀` is `L`
(`RingTheory.DepthTwo.etale_finite_away_integralClosure_of_irreducible`); at the primes of the
closed fibre this is purity (`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`).
This is used in the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace RingTheory.DepthTwo

variable {R₀ B Bk L : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
  [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]

omit [Algebra.Smooth R₀ B] in
include Bk in
/-- **The integral closure away from the closed fibre**: inverting a uniformizer `ϖ` of `R₀`,
the integral closure of `B` in `L` becomes `L`, which is finite étale. -/
theorem etale_finite_away_integralClosure_of_irreducible {ϖ : R₀} (hϖ : Irreducible ϖ) :
    Algebra.Etale (Localization.Away (algebraMap R₀ B ϖ))
        (Localization.Away (algebraMap R₀ B ϖ) ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.Away (algebraMap R₀ B ϖ))
        (Localization.Away (algebraMap R₀ B ϖ) ⊗[B] integralClosure B L) := by
  let Bh := Localization.Away (algebraMap R₀ B ϖ)
  let T₀ := integralClosure B L
  have hunit (x : Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) :
      IsUnit (algebraMap B Bh x) := by
    obtain ⟨_, ⟨r, hr, rfl⟩⟩ := x
    obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hr) hϖ
    have hϖu : IsUnit (algebraMap B Bh (algebraMap R₀ B ϖ)) :=
      IsLocalization.Away.algebraMap_isUnit _
    simp only [hv, map_mul, map_pow]
    exact ((v.isUnit.map (algebraMap R₀ B)).map (algebraMap B Bh)).mul (hϖu.pow m)
  let : Algebra Bk Bh := (IsLocalization.lift (M := Algebra.algebraMapSubmonoid B
    (nonZeroDivisors R₀)) (S := Bk) hunit).toAlgebra
  have : IsScalarTower B Bk Bh := .of_algebraMap_eq fun b ↦
    (IsLocalization.lift_eq (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))
      (S := Bk) hunit b).symm
  let e₁ : Bk ⊗[B] T₀ ≃ₐ[Bk] L := tensorIntegralClosureEquiv (R₀ := R₀)
  have : Algebra.Etale Bk (Bk ⊗[B] T₀) := .of_equiv e₁.symm
  have : Module.Finite Bk (Bk ⊗[B] T₀) := .equiv e₁.symm.toLinearEquiv
  let e : Bh ⊗[Bk] (Bk ⊗[B] T₀) ≃ₐ[Bh] Bh ⊗[B] T₀ :=
    Algebra.TensorProduct.cancelBaseChange B Bk Bh Bh T₀
  exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩

omit [IsDiscreteValuationRing R₀] [Algebra.Smooth R₀ B] [Module.Finite Bk L] [Algebra.Etale Bk L] in
include Bk in
/-- The nonzero elements of `R₀` are invertible in `L`. -/
lemma isUnit_algebraMap_of_ne_zero {r : R₀} (hr : r ≠ 0) :
    IsUnit (algebraMap B L (algebraMap R₀ B r)) := by
  rw [IsScalarTower.algebraMap_apply B Bk L]
  exact (IsLocalization.map_units Bk
    (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ :
      nonZeroDivisors R₀)⟩ : Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))).map _

omit [Algebra.Smooth R₀ B] in
/-- A prime of `B` not over the maximal ideal of `R₀` does not contain a uniformizer. -/
lemma algebraMap_notMem_of_comap_ne {ϖ : R₀} (hϖ : Irreducible ϖ) (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R₀ B) ≠ maximalIdeal R₀) : algebraMap R₀ B ϖ ∉ Q := by
  intro h
  refine hQ ((IsLocalRing.maximalIdeal.isMaximal R₀).eq_of_le (Ideal.IsPrime.comap _).ne_top
    ?_).symm
  rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
  exact h

include Bk in
/-- **Purity over a discrete valuation ring**, local form: if the integral closure `T₀` of `B` in
`L` is finite étale at the minimal primes of `𝔪 B`, then it is finite étale near every prime. -/
theorem exists_etale_away_integralClosure_of_minimalPrimes
    (H : ∀ Q : Ideal B, [Q.IsPrime] →
      Q ∈ ((maximalIdeal R₀).map (algebraMap R₀ B)).minimalPrimes →
      Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B] integralClosure B L))
    (Q : Ideal B) [Q.IsPrime] :
    ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  let : Algebra R₀ L := ((algebraMap B L).comp (algebraMap R₀ B)).toAlgebra
  have : IsScalarTower R₀ B L := .of_algebraMap_eq' rfl
  have hunit (r : R₀) (hr : r ≠ 0) : IsUnit (algebraMap R₀ L r) :=
    isUnit_algebraMap_of_ne_zero (B := B) (Bk := Bk) hr
  have hgen := etale_finite_away_integralClosure_of_irreducible (B := B) (Bk := Bk) (L := L) hϖ
  have hm0 : maximalIdeal R₀ ≠ ⊥ := IsDiscreteValuationRing.not_a_field R₀
  by_cases hQ : Q.comap (algebraMap R₀ B) = maximalIdeal R₀
  swap
  · exact ⟨_, algebraMap_notMem_of_comap_ne hϖ Q hQ, hgen⟩
  refine exists_etale_integralClosure_of_smooth (maximalIdeal R₀) hm0 hunit Q hQ
    fun Q' hQ' _ hor ↦ ?_
  by_cases hQ'm : Q'.comap (algebraMap R₀ B) = maximalIdeal R₀
  swap
  · exact ⟨_, algebraMap_notMem_of_comap_ne hϖ Q' hQ'm, hgen⟩
  have hmin : Q' ∈ ((maximalIdeal R₀).map (algebraMap R₀ B)).minimalPrimes :=
    hor.resolve_left (not_not.2 hQ'm)
  obtain ⟨hE, hF⟩ := H Q' hmin
  refine exists_etale_finite_away_of_localization hunit Q' (by rw [hQ'm]; exact hm0)
    fun Q'' hQ'' hlt ↦ ⟨_, algebraMap_notMem_of_comap_ne hϖ Q'' fun h ↦ ?_, hgen⟩
  have hle : (maximalIdeal R₀).map (algebraMap R₀ B) ≤ Q'' := by
    rw [Ideal.map_le_iff_le_comap, h]
  exact hlt.not_ge (hmin.2 ⟨hQ'', hle⟩ hlt.le)

include Bk in
/-- **Purity over a discrete valuation ring.** If the integral closure `T₀` of `B` in `L` is
finite étale at the minimal primes of `𝔪 B`, then `D ⊗[B] T₀` is finite étale over `D`, of rank
at most the rank of `L`, for every `B`-algebra `D`. -/
theorem etale_finite_tensor_integralClosure_of_minimalPrimes {k : ℕ}
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p ≤ k)
    (H : ∀ Q : Ideal B, [Q.IsPrime] →
      Q ∈ ((maximalIdeal R₀).map (algebraMap R₀ B)).minimalPrimes →
      Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B] integralClosure B L))
    (D : Type u) [CommRing D] [Algebra B D] :
    Algebra.Etale D (D ⊗[B] integralClosure B L) ∧ Module.Finite D (D ⊗[B] integralClosure B L) ∧
      ∀ p, Module.rankAtStalk (R := D) (D ⊗[B] integralClosure B L) p ≤ k := by
  refine Algebra.etale_finite_tensor_of_forall_isPrime fun Q hQ ↦ ?_
  obtain ⟨h, hh, hE, -⟩ :=
    exists_etale_away_integralClosure_of_minimalPrimes (Bk := Bk) H (Q.comap (algebraMap B D))
  exact ⟨h, hh, hE, finite_rankAtStalk_le_of_etale (R₀ := R₀) (Bk := Bk) h hrank⟩

end RingTheory.DepthTwo
