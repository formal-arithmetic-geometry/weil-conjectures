/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.AlgebraicGeometry.PrimitiveRootsCover
public import WeilConjectures.RingTheory.Etale.IntegrallyClosed

/-!
# Adjoining roots of unity to a discrete valuation ring by a local étale extension

Let `A` be a discrete valuation ring and `n` a natural number invertible in `A`. Then there is a
discrete valuation ring `A₁` with a local étale, faithfully flat map `A → A₁` such that `A₁`
contains a primitive `n`-th root of unity
(`IsDiscreteValuationRing.exists_etale_isPrimitiveRoot`).

The ring `A₁` is a localization `D[1/s]` of the étale `A`-algebra
`D = A[ζ] = A[T]/(Tⁿ - 1)[(1 - ζᵏ)⁻¹, 0 < k < n]` (`AlgebraicGeometry.PrimitiveRootsAlgebra`)
which is local: `D` has finitely many primes (it is quasi-finite over `A`), so a prime `q` of
`D` over the maximal ideal of `A` has a basic open neighbourhood consisting of generalizations of
`q` (`Ideal.exists_notMem_forall_le_of_finite`), and on it `D[1/s] = D_q`.

This is used in the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`).
-/

@[expose] public section

universe u

open IsLocalRing Polynomial

/-- In a ring with finitely many primes, every prime `q` has a basic open neighbourhood
`D(s)` consisting of generalizations of `q`: there is `s ∉ q` such that every prime not
containing `s` is contained in `q`. -/
theorem Ideal.exists_notMem_forall_le_of_finite {C : Type*} [CommRing C]
    [Finite (PrimeSpectrum C)] (q : Ideal C) [q.IsPrime] :
    ∃ s ∉ q, ∀ p : Ideal C, p.IsPrime → s ∉ p → p ≤ q := by
  classical
  have := Fintype.ofFinite (PrimeSpectrum C)
  have h (p : PrimeSpectrum C) : ∃ t : C, ¬ p.asIdeal ≤ q → t ∈ p.asIdeal ∧ t ∉ q := by
    by_cases hp : p.asIdeal ≤ q
    · exact ⟨0, fun h ↦ (h hp).elim⟩
    · obtain ⟨t, ht, htq⟩ := Set.not_subset.mp hp
      exact ⟨t, fun _ ↦ ⟨ht, htq⟩⟩
  choose t ht using h
  let S := Finset.univ.filter (fun p : PrimeSpectrum C ↦ ¬ p.asIdeal ≤ q)
  refine ⟨∏ p ∈ S, t p, ?_, fun p hp hs ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hpS, hpq⟩
    exact (ht p (Finset.mem_filter.mp hpS).2).2 hpq
  · by_contra hpq
    have hpS : (⟨p, hp⟩ : PrimeSpectrum C) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩
    exact hs (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem t hpS) (ht ⟨p, hp⟩ hpq).1)

/-- If `s ∉ q` and every prime not containing `s` is contained in the prime `q`, then the
localization `C[1/s]` is the localization of `C` at `q`. -/
theorem IsLocalization.Away.isLocalization_atPrime {C : Type*} [CommRing C] (q : Ideal C)
    [q.IsPrime] {s : C} (hs : s ∉ q) (h : ∀ p : Ideal C, p.IsPrime → s ∉ p → p ≤ q)
    (Cs : Type*) [CommRing Cs] [Algebra C Cs] [IsLocalization.Away s Cs] :
    IsLocalization.AtPrime Cs q := by
  refine IsLocalization.of_le (Submonoid.powers s) q.primeCompl
    ((Submonoid.powers_le (P := q.primeCompl)).mpr hs) fun r hr ↦ ?_
  by_contra hu
  obtain ⟨M, hM, hrM⟩ := exists_max_ideal_of_mem_nonunits hu
  have hsM : s ∉ M.comap (algebraMap C Cs) := fun hsM ↦
    hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hsM (IsLocalization.Away.algebraMap_isUnit s))
  exact hr (h _ (Ideal.comap_isPrime _ M) hsM hrM)

/-- A discrete valuation ring has finitely many primes: `⊥` and the maximal ideal. -/
instance IsDiscreteValuationRing.finite_primeSpectrum (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : Finite (PrimeSpectrum A) := by
  refine Finite.of_injective (fun p : PrimeSpectrum A ↦ (p.asIdeal = ⊥ : Prop)) fun p₁ p₂ h ↦ ?_
  have key (p : PrimeSpectrum A) (hp : p.asIdeal ≠ ⊥) : p.asIdeal = maximalIdeal A :=
    eq_maximalIdeal (p.2.isMaximal hp)
  ext1
  by_cases h₁ : p₁.asIdeal = ⊥
  · rw [h₁, cast h h₁]
  · rw [key p₁ h₁, key p₂ fun h₂ ↦ h₁ (cast h.symm h₂)]

/-- **Adjoining roots of unity to a DVR.** Let `A` be a discrete valuation ring and `n` a
natural number invertible in `A`. Then there is a discrete valuation ring `A₁` with a local,
étale, faithfully flat map `A → A₁` such that `A₁` contains a primitive `n`-th root of unity.

Used in the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`). -/
theorem IsDiscreteValuationRing.exists_etale_isPrimitiveRoot {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] {n : ℕ} (hn : IsUnit (n : A)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁), Algebra.Etale A A₁ ∧ IsLocalHom (algebraMap A A₁) ∧
        Module.FaithfullyFlat A A₁ ∧ ∃ ζ : A₁, IsPrimitiveRoot ζ n := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  let D := AlgebraicGeometry.PrimitiveRootsAlgebra A n
  have : Algebra.Etale A D := AlgebraicGeometry.PrimitiveRootsAlgebra.etale A n hn₀ hn
  -- a prime `q` of `D` over the maximal ideal of `A`
  let Ω := AlgebraicClosure (ResidueField A)
  let φ : A →+* Ω := (algebraMap (ResidueField A) Ω).comp (residue A)
  have : NeZero (n : Ω) := ⟨by simpa [φ] using (hn.map φ).ne_zero⟩
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.PrimitiveRootsAlgebra.exists_lift A n φ
  let q := RingHom.ker ψ
  have : q.IsPrime := RingHom.ker_isPrime ψ
  have hq : q.comap (algebraMap A D) = maximalIdeal A := by
    rw [RingHom.comap_ker, hψ, RingHom.ker_comp_of_injective _
      (algebraMap (ResidueField A) Ω).injective, ker_residue]
  -- the localization `A₁ = D[1/s] = D_q`
  have : Finite (PrimeSpectrum D) := Algebra.QuasiFinite.finite_primeSpectrum A D
  obtain ⟨s, hs, hsq⟩ := q.exists_notMem_forall_le_of_finite
  let A₁ := Localization.Away s
  have : IsLocalization.AtPrime A₁ q := IsLocalization.Away.isLocalization_atPrime q hs hsq A₁
  have : IsLocalRing A₁ := IsLocalization.AtPrime.isLocalRing A₁ q
  have : Algebra.Etale A A₁ := Algebra.Etale.comp A D A₁
  have : IsDomain A₁ :=
    (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization (R := A) q A₁).1
  have hloc : IsLocalHom (algebraMap A A₁) := by
    refine ((local_hom_TFAE (algebraMap A A₁)).out 0 4).mpr ?_
    rw [IsScalarTower.algebraMap_eq A D A₁, ← Ideal.comap_comap]
    exact (congrArg (Ideal.comap (algebraMap A D))
      (IsLocalization.AtPrime.under_maximalIdeal A₁ q)).trans hq
  have : Module.FaithfullyFlat A A₁ := .of_flat_of_isLocalHom
  have : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing A A₁
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : maximalIdeal A₁ = Ideal.span {algebraMap A A₁ ϖ} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A), hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField A₁ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A A₁)]
    exact hϖ.ne_zero
  have : IsDiscreteValuationRing A₁ :=
    ((IsDiscreteValuationRing.TFAE A₁ hnf).out 0 4).mpr
      (⟨⟨_, hmax⟩⟩ : (maximalIdeal A₁).IsPrincipal)
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hloc,
    inferInstance, algebraMap D A₁ (AlgebraicGeometry.PrimitiveRootsAlgebra.zeta A n), ?_⟩
  refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hn₀) ?_ fun l hl₀ hln hl ↦ ?_
  · rw [← map_pow, AlgebraicGeometry.PrimitiveRootsAlgebra.zeta_pow, map_one]
  · have hu := (AlgebraicGeometry.PrimitiveRootsAlgebra.isUnit_one_sub_zeta_pow A n hl₀
      hln).map (algebraMap D A₁)
    have h0 :
        algebraMap D A₁ (1 - AlgebraicGeometry.PrimitiveRootsAlgebra.zeta A n ^ l) = 0 := by
      rw [map_sub, map_pow, hl]
      exact sub_eq_zero.mpr (map_one _)
    exact not_isUnit_zero (h0 ▸ hu)
