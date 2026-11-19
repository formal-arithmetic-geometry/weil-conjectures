/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiSymmetry
public import WeilConjectures.ZetaFunction.Rationality
public import WeilConjectures.ZetaFunction.WeightSeparation
public import WeilConjectures.ZetaLinearAlgebra.GaloisStrata

/-!
# Realization independence of the integral Frobenius factors

Let `X₀` be smooth and proper of pure dimension `d` over `k₀ = 𝔽_q`.
The zeta series `Z(X₀, T)` has a unique normalized reduced integral presentation `Z = A / B`
(`A, B ∈ ℤ[T]`, `A(0) = B(0) = 1`, `A` and `B` coprime in `ℚ[T]`,
`AlgebraicGeometry.Scheme.Hom.existsUnique_isNormalizedIntegralFraction_zetaSeries`). This file
identifies it with
the parity products of the integral Frobenius factors `Pᵢ`, `A = ∏_{i odd} Pᵢ` and
`B = ∏_{i even} Pᵢ`, so that `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ` for every `ℓ ≠ p`; and it recovers
each `Pᵢ` from `A` and `B` alone, without reference to `ℓ`: `Pᵢ` is the stratum polynomial
`Qᵢ = ∏ (1 - α T)`, the product over the reciprocal roots `α` of `A` (`i` odd) or `B` (`i` even)
which are `q`-Weil numbers of weight `i`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_isWeilNumber_of_mem_roots_reverse`: every reciprocal root of `A`
  (resp. `B`) is a `q`-Weil number of some odd (resp. even) weight `0 ≤ i ≤ 2d`.
- `AlgebraicGeometry.Scheme.integral_recovery`: the integral Frobenius factors and the
  identification of the normalized presentation with their parity products.
- `AlgebraicGeometry.Scheme.realization_independence`: the stratum polynomials `Qᵢ` of the
  normalized presentation are integral, and their scalar extension along every `ℓ`-adic
  realization `ℚ̄ ≃ ℚ̄^{(ℓ)} ⊆ ℚ̄_ℓ` is `P_{i,ℓ}`.
- `AlgebraicGeometry.Scheme.riemann_hypothesis_of_isIntegralFrobeniusFactor`: the reciprocal
  roots of `Pᵢ` are algebraic integers and `q`-Weil numbers of weight `i`, and are the Frobenius
  eigenvalues on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀]

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]

section ParityProducts

variable {k₀ X d}

/-- The parity products `∏_{i odd} Pᵢ` and `∏_{i even} Pᵢ` of the integral Frobenius factors are
a normalized reduced integral presentation of `Z(X₀, T)`: their constant coefficients are `1`,
they factor the zeta series, and they are coprime in `ℚ[T]` since their scalar extensions
`N_ℓ`, `D_ℓ` are coprime. -/
theorem isNormalizedIntegralFraction_prod {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P i)
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P i) := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  have h0 (i : Fin (2 * d + 1)) : (P i).coeff 0 = 1 := by
    have h := congrArg (fun Q : Polynomial (PadicAlgCl l) ↦ Q.coeff 0) (hP i l)
    simp only [Polynomial.coeff_map, eq_intCast, coeff_zero_frobeniusCharpolyRev] at h
    exact_mod_cast h
  have hmap (Q : Polynomial ℤ) : (Q.map (Int.castRingHom ℚ)).map (algebraMap ℚ (PadicAlgCl l)) =
      Q.map (Int.castRingHom (PadicAlgCl l)) := by
    rw [Polynomial.map_map]
    congr 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_zero_prod]
    exact Finset.prod_eq_one fun i _ ↦ h0 i
  · rw [coeff_zero_prod]
    exact Finset.prod_eq_one fun i _ ↦ h0 i
  · refine (isCoprime_map (algebraMap ℚ (PadicAlgCl l))).1 ?_
    rw [hmap, hmap, map_prod_odd_eq_oddFrobeniusProduct hP l,
      map_prod_even_eq_evenFrobeniusProduct hP l]
    exact isCoprime_oddFrobeniusProduct_evenFrobeniusProduct k₀ l X d
  · have hc (s : Finset (Fin (2 * d + 1))) :
        ((∏ i ∈ s, P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
          ∏ i ∈ s, ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
      rw [Polynomial.map_prod]
      exact map_prod Polynomial.coeToPowerSeries.ringHom _ _
    rw [hc, hc]
    exact zetaSeries_mul_prod_even_eq_prod_odd_of_isIntegralFrobeniusFactor k₀ X d hP

end ParityProducts

section ReciprocalRoots

/-- The weights of the reciprocal roots of the zeta function: let `Z(X₀, T) = A / B` be the
normalized reduced integral presentation of the zeta series of `X₀`, smooth and proper of pure
dimension `d` over `k₀ = 𝔽_q`. For every reciprocal root `α ∈ ℂ`
of `A` (resp. of `B`) there is an odd (resp. even) integer `0 ≤ i ≤ 2d` such that `α` is a `q`-Weil
number of weight `i`: `|τ(α)| = q^{i/2}` for every field embedding `τ : ℚ(α) → ℂ`.

For a prime `ℓ ≠ p`, `A^{(ℓ)} = N_ℓ = ∏_{i odd} P_{i,ℓ}` and `B^{(ℓ)} = D_ℓ = ∏_{i even} P_{i,ℓ}`
(`AlgebraicGeometry.Scheme.map_eq_frobeniusProduct_of_isNormalizedIntegralFraction`), so under an
embedding `ι : ℚ̄_ℓ → ℂ` the reciprocal root `α` is a reciprocal root of some `ι P_{i,ℓ}` of the
right parity, and these are `q`-Weil numbers of weight `i`
(`AlgebraicGeometry.Scheme.isUniversallyPureOfWeight_map_frobeniusCharpolyRev`). -/
theorem exists_isWeilNumber_of_mem_roots_reverse {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    (∀ α ∈ (A.reverse.map (Int.castRingHom ℂ)).roots,
      ∃ i : ℕ, i ≤ 2 * d ∧ Odd i ∧ IsWeilNumber (Nat.card k₀) i α) ∧
    ∀ α ∈ (B.reverse.map (Int.castRingHom ℂ)).roots,
      ∃ i : ℕ, i ≤ 2 * d ∧ Even i ∧ IsWeilNumber (Nat.card k₀) i α := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  obtain ⟨hA, hB⟩ := map_eq_frobeniusProduct_of_isNormalizedIntegralFraction k₀ X d l hAB
  have hmap (C : Polynomial ℤ) : C.map (Int.castRingHom ℂ) =
      (C.map (Int.castRingHom (PadicAlgCl l))).map ι := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  -- a reciprocal root of a product of factors `P_{j,ℓ}`, `j ∈ s`, is a Weil number of weight `j`
  -- for some `j ∈ s`
  have key (C : Polynomial ℤ) (s : Finset ℕ) (hs : s ⊆ Finset.range (2 * d + 1))
      (hC : C.map (Int.castRingHom (PadicAlgCl l)) = ∏ j ∈ s, frobeniusCharpolyRev k₀ l X j)
      (α : ℂ) (hα : α ∈ (C.reverse.map (Int.castRingHom ℂ)).roots) :
      ∃ j ∈ s, IsWeilNumber (Nat.card k₀) j α := by
    have hC0 : C.map (Int.castRingHom ℂ) ≠ 0 := by
      rw [hmap, hC, Polynomial.map_prod]
      exact Finset.prod_ne_zero_iff.2 fun j _ ↦
        (isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι j).ne_zero
    rw [← Polynomial.reverse_map (RingHom.injective_int _), Polynomial.mem_roots_reverse_iff hC0]
      at hα
    obtain ⟨hα0, hroot⟩ := hα
    rw [hmap, hC, Polynomial.map_prod, Polynomial.IsRoot, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at hroot
    obtain ⟨j, hj, hroot⟩ := hroot
    refine ⟨j, hj, ?_⟩
    have hj' : j ≤ 2 * d := by
      have := Finset.mem_range.1 (hs hj)
      omega
    have hz : α⁻¹ ∈ ((frobeniusCharpolyRev k₀ l X j).map ι).roots :=
      (Polynomial.mem_roots (isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι j).ne_zero).2 hroot
    have h := (isUniversallyPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι hj').2 _ hz
    rw [isUniversallyPureOfWeight_iff_isWeilNumber_inv (inv_ne_zero hα0), inv_inv] at h
    exact h
  refine ⟨fun α hα ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨j, hj, h⟩ := key A ((Finset.range (2 * d + 1)).filter Odd)
      (fun j hj ↦ (Finset.mem_filter.1 hj).1) (by rw [hA, oddFrobeniusProduct]) α hα
    obtain ⟨hj, hodd⟩ := Finset.mem_filter.1 hj
    exact ⟨j, by have := Finset.mem_range.1 hj; omega, hodd, h⟩
  · obtain ⟨j, hj, h⟩ := key B ((Finset.range (2 * d + 1)).filter Even)
      (fun j hj ↦ (Finset.mem_filter.1 hj).1) (by rw [hB, evenFrobeniusProduct]) α hα
    obtain ⟨hj, heven⟩ := Finset.mem_filter.1 hj
    exact ⟨j, by have := Finset.mem_range.1 hj; omega, heven, h⟩

/-- Every algebraic reciprocal root of the normalized zeta numerator or denominator becomes a
Frobenius eigenvalue after any embedding into an ℓ-adic algebraic closure. The degree has the
parity of the polynomial from which the root came. -/
theorem exists_frobeniusEigenvalue_of_mem_roots_reverse {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (θ : AlgebraicClosure ℚ →+* PadicAlgCl l) :
    (∀ α ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots,
      ∃ i : ℕ, i ≤ 2 * d ∧ Odd i ∧
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ α)) ∧
    (∀ α ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots,
      ∃ i : ℕ, i ≤ 2 * d ∧ Even i ∧
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ α)) := by
  obtain ⟨hA, hB⟩ := map_eq_frobeniusProduct_of_isNormalizedIntegralFraction k₀ X d l hAB
  have hcomp : θ.comp (algebraMap ℤ (AlgebraicClosure ℚ)) =
      Int.castRingHom (PadicAlgCl l) := RingHom.ext_int _ _
  have key (C : Polynomial ℤ) (h0 : C.coeff 0 = 1) (s : Finset ℕ)
      (hC : C.map (Int.castRingHom (PadicAlgCl l)) =
        ∏ j ∈ s, frobeniusCharpolyRev k₀ l X j)
      (α : AlgebraicClosure ℚ)
      (hα : α ∈ (C.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) :
      ∃ j ∈ s,
        ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobeniusEnd.HasEigenvalue (θ α) := by
    have hrev0 : C.reverse.map (Int.castRingHom (PadicAlgCl l)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2
        (Polynomial.monic_reverse_of_coeff_zero_eq_one h0).ne_zero
    have hroot : (C.reverse.map (Int.castRingHom (PadicAlgCl l))).IsRoot (θ α) := by
      have h := (Polynomial.mem_roots'.1 hα).2.map (f := θ)
      simpa only [Polynomial.map_map, hcomp] using h
    have hα' : θ α ∈ (C.reverse.map (Int.castRingHom (PadicAlgCl l))).roots :=
      (Polynomial.mem_roots hrev0).2 hroot
    have hC0 : C.map (Int.castRingHom (PadicAlgCl l)) ≠ 0 := by
      intro he
      have he0 := congrArg (fun P : Polynomial (PadicAlgCl l) ↦ P.coeff 0) he
      simp only [Polynomial.coeff_map, h0, map_one] at he0
      simp at he0
    rw [← Polynomial.reverse_map (RingHom.injective_int _),
      Polynomial.mem_roots_reverse_iff hC0] at hα'
    obtain ⟨hα0, hroot'⟩ := hα'
    rw [hC, Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hroot'
    obtain ⟨j, hj, hjroot⟩ := hroot'
    have hP0 : frobeniusCharpolyRev k₀ l X j ≠ 0 := by
      intro he
      have he0 := congrArg (fun P : Polynomial (PadicAlgCl l) ↦ P.coeff 0) he
      simp [coeff_zero_frobeniusCharpolyRev] at he0
    have hmem : θ α ∈ (frobeniusCharpolyRev k₀ l X j).reverse.roots := by
      apply (Polynomial.mem_roots_reverse_iff hP0).2
      exact ⟨hα0, hjroot⟩
    rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial,
      (LinearMap.reciprocal_roots_eigenvalues
        ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobeniusEnd
        (LinearEquiv.isUnit_det' ((WeilSheaf.adicConstant k₀ l X).cohomology j).frobenius)).1]
      at hmem
    exact ⟨j, hj, (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2
      (Polynomial.isRoot_of_mem_roots hmem)⟩
  refine ⟨fun α hα ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨j, hj, heig⟩ := key A hAB.1 _
      (by rw [hA, oddFrobeniusProduct]) α hα
    obtain ⟨hjrange, hodd⟩ := Finset.mem_filter.1 hj
    exact ⟨j, by have := Finset.mem_range.1 hjrange; omega, hodd, heig⟩
  · obtain ⟨j, hj, heig⟩ := key B hAB.2.1 _
      (by rw [hB, evenFrobeniusProduct]) α hα
    obtain ⟨hjrange, heven⟩ := Finset.mem_filter.1 hj
    exact ⟨j, by have := Finset.mem_range.1 hjrange; omega, heven, heig⟩

end ReciprocalRoots

/-- For `X₀` smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`,
and `Z(X₀, T) = A / B` the normalized reduced integral presentation of its zeta series:

* for every `0 ≤ i ≤ 2d` there is a unique `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1` and
  `Pᵢ^{(ℓ)} = P_{i,ℓ}` for every prime `ℓ ≠ p` (the integral Frobenius factors);
* `A = ∏_{i odd} Pᵢ` and `B = ∏_{i even} Pᵢ`, hence `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ` for every
  `ℓ ≠ p`;
* `Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`;
* `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`.

The normalized presentation is unique, and the parity
products of the `Pᵢ` are one (`AlgebraicGeometry.Scheme.isNormalizedIntegralFraction_prod`). -/
theorem integral_recovery [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    (∀ i : ℕ, i ≤ 2 * d →
      ∃! P : Polynomial ℤ, P.coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X i P) ∧
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      A = ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P i ∧
      B = ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P i ∧
      (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
        A.map (Int.castRingHom (PadicAlgCl l)) = oddFrobeniusProduct k₀ l X d ∧
        B.map (Int.castRingHom (PadicAlgCl l)) = evenFrobeniusProduct k₀ l X d) ∧
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P ∧
      ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : Fin (2 * d + 1)),
        (P i).natDegree = Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier := by
  obtain ⟨P, hfact, -, -, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  obtain ⟨p, -, huniq⟩ :=
    (X ↘ Spec (CommRingCat.of k₀)).existsUnique_isNormalizedIntegralFraction_zetaSeries
  have hA := (huniq (A, B) hAB).trans (huniq ⟨_, _⟩ (isNormalizedIntegralFraction_prod hP)).symm
  simp only [Prod.mk.injEq] at hA
  obtain ⟨rfl, rfl⟩ := hA
  exact ⟨fun _ hi ↦ existsUnique_isIntegralFrobeniusFactor k₀ X d hi, P,
    fun i ↦ ⟨hfact.coeff_zero_eq_one i, hP i⟩, rfl, rfl,
    fun l _ _ ↦ ⟨map_prod_odd_eq_oddFrobeniusProduct hP l,
      map_prod_even_eq_evenFrobeniusProduct hP l⟩, hfact,
    fun l _ _ i ↦ natDegree_eq_finrank_of_isIntegralFrobeniusFactor k₀ X (hP i) l⟩

/-- For `X₀` smooth and proper of pure dimension `d` over
`k₀ = 𝔽_q`, `Z(X₀, T) = A / B` the normalized reduced integral presentation of its zeta series
and `0 ≤ i ≤ 2d`, let `Qᵢ = ∏_{α ∈ Rᵢ} (1 - α T)` be the stratum polynomial of the multiset `Rᵢ`
of reciprocal roots in `ℚ̄` of `A` (`i` odd) or `B` (`i` even) which are `q`-Weil numbers of
weight `i` (`Polynomial.weilStratumPoly`). Then

* `Qᵢ` has integer coefficients and `Qᵢ(0) = 1`;
* for every prime `ℓ ≠ p` and every `ℓ`-adic realization `ρ : ℚ̄ ≃ ℚ̄^{(ℓ)} ⊆ ℚ̄_ℓ`
  (`AlgebraicRealization`), the scalar extension of `Qᵢ` along `ρ` is `P_{i,ℓ}`;
* `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ`.

By `AlgebraicGeometry.Scheme.exists_isIntegralFrobeniusFactor_of_isNormalizedIntegralFraction`,
`A` and `B` are the parity products of the
integral Frobenius factors `Pⱼ`, whose reciprocal roots are `q`-Weil numbers of weight `j` (the
Riemann hypothesis for the `Pⱼ`,
`AlgebraicGeometry.Scheme.weilRiemannHypothesis_of_isIntegralFrobeniusFactor`); so the
weight-`i` stratum of `A` or `B` is the reciprocal-root
multiset of `Pᵢ` (`Polynomial.weilStratum_prod`), and `Qᵢ = Pᵢ`. -/
theorem realization_independence {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) {i : ℕ} (hi : i ≤ 2 * d) :
    (∃ Q : Polynomial ℤ, Q.coeff 0 = 1 ∧ Q.map (algebraMap ℤ (AlgebraicClosure ℚ)) =
      weilStratumPoly (Nat.card k₀) i (if Odd (i : ℤ) then A else B)) ∧
    (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (ρ : AlgebraicRealization (PadicAlgCl l)),
      (weilStratumPoly (Nat.card k₀) i (if Odd (i : ℤ) then A else B)).map
          (((_root_.algebraicClosure ℚ (PadicAlgCl l)).val.comp
            (ρ : AlgebraicClosure ℚ →ₐ[ℚ] _root_.algebraicClosure ℚ (PadicAlgCl l))) :
            AlgebraicClosure ℚ →+* PadicAlgCl l) =
        frobeniusCharpolyRev k₀ l X i) ∧
    ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
      A.map (Int.castRingHom (PadicAlgCl l)) = oddFrobeniusProduct k₀ l X d ∧
      B.map (Int.castRingHom (PadicAlgCl l)) = evenFrobeniusProduct k₀ l X d := by
  obtain ⟨P, hP, rfl, rfl⟩ :=
    exists_isIntegralFrobeniusFactor_of_isNormalizedIntegralFraction k₀ X d hAB
  have hrh := weilRiemannHypothesis_of_isIntegralFrobeniusFactor k₀ X d fun i ↦ (hP i).2
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  set j : Fin (2 * d + 1) := ⟨i, by omega⟩
  -- the stratum polynomial is `Pᵢ`
  have hQ : weilStratumPoly (Nat.card k₀) i
      (if Odd (i : ℤ) then ∏ k ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P k
        else ∏ k ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P k) =
      (P j).map (algebraMap ℤ (AlgebraicClosure ℚ)) := by
    have hw : Set.InjOn (fun k : Fin (2 * d + 1) ↦ (k.1 : ℤ)) Set.univ := fun a _ b _ h ↦
      Fin.ext (by simpa using h)
    have key (s : Finset (Fin (2 * d + 1))) (hj : j ∈ s) :
        weilStratumPoly (Nat.card k₀) (j.1 : ℤ) (∏ k ∈ s, P k) =
          (P j).map (algebraMap ℤ (AlgebraicClosure ℚ)) :=
      weilStratumPoly_prod s P (fun k ↦ (k.1 : ℤ)) hq (hw.mono (Set.subset_univ _))
        (fun k _ ↦ (hP k).1)
        (fun k _ y hy ↦ by
          rw [hrh.norm_eq_of_mem_roots_reverse (fun k ↦ (hP k).1) k hy, Int.cast_natCast])
        hj
    split_ifs with h
    · exact key _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, by exact_mod_cast h⟩)
    · exact key _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, by
        rw [← Nat.not_odd_iff_even]; exact fun h' ↦ h (by exact_mod_cast h')⟩)
  refine ⟨⟨P j, (hP j).1, hQ.symm⟩, fun l _ _ ρ ↦ ?_,
    fun l _ _ ↦ map_eq_frobeniusProduct_of_isNormalizedIntegralFraction k₀ X d l hAB⟩
  rw [hQ, Polynomial.map_map, ← (hP j).2 l]
  congr 1
  exact RingHom.ext_int _ _

/-- A `q`-Weil number `α ∈ ℂ` of weight `w` has absolute value `q^{w/2}`: `α` is a complex root of
its own minimal polynomial. -/
private theorem norm_eq_of_isWeilNumber {q : ℕ} {w : ℝ} {α : ℂ} (h : IsWeilNumber q w α) :
    ‖α‖ = (q : ℝ) ^ (w / 2) := by
  rw [isWeilNumber_iff] at h
  exact h.2 α (Polynomial.mem_aroots.2 ⟨minpoly.ne_zero h.1, minpoly.aeval ℚ α⟩)

/-- **The Riemann hypothesis for the integral Frobenius factors.** For `X₀` smooth and proper of
pure dimension `d` over `k₀ = 𝔽_q` and an integral Frobenius factor `P` in degree `i ≤ 2d`:

* every reciprocal root `α ∈ ℂ` of `P` (a root of `P^#(U) = U^{deg P} P(U⁻¹)`) is an algebraic
  integer and a `q`-Weil number of weight `i`: `|τ(α)| = q^{i/2}` for every embedding
  `τ : ℚ(α) → ℂ`;
* every ordinary root `β` (a root of `P`) is a `q`-Weil number of weight `-i`;
* for every prime `ℓ ≠ p`, the reciprocal roots of `P` in `ℚ̄_ℓ` are eigenvalues of the
  geometric Frobenius on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`.

`P` is the factor `Pᵢ` of the normalized presentation `Z(X₀, T) = A / B`, `A = ∏_{j odd} Pⱼ`,
`B = ∏_{j even} Pⱼ`; its reciprocal roots are reciprocal roots of `A` or `B`, hence `q`-Weil
numbers of some weight of the parity of `i`
(`AlgebraicGeometry.Scheme.exists_isWeilNumber_of_mem_roots_reverse`), and their absolute value
`q^{i/2}` (purity of `P_{i,ℓ}`) forces the weight `i`. They are algebraic integers as roots of the
monic integer polynomial `P^#`. -/
theorem riemann_hypothesis_of_isIntegralFrobeniusFactor {i : ℕ} (hi : i ≤ 2 * d) {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) :
    (∀ α ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      _root_.IsIntegral ℤ α ∧ IsWeilNumber (Nat.card k₀) i α) ∧
    (∀ β ∈ (P.map (Int.castRingHom ℂ)).roots, IsWeilNumber (Nat.card k₀) (-(i : ℝ)) β) ∧
    ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
      ∀ α ∈ (P.reverse.map (Int.castRingHom (PadicAlgCl l))).roots,
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue α := by
  obtain ⟨l₀, hl₀, hne₀⟩ := exists_prime_ne_ringChar k₀
  have : Fact l₀.Prime := ⟨hl₀⟩
  have : Fact (ringChar k₀ ≠ l₀) := ⟨hne₀⟩
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l₀
  -- the normalized presentation `Z = A / B` and the integral factors `A = ∏_{j odd} Pⱼ`,
  -- `B = ∏_{j even} Pⱼ`; `P` is the factor `Pᵢ`
  obtain ⟨p, hAB, -⟩ :=
    (X ↘ Spec (CommRingCat.of k₀)).existsUnique_isNormalizedIntegralFraction_zetaSeries
  obtain ⟨hA, hB⟩ := exists_isWeilNumber_of_mem_roots_reverse k₀ X d hAB
  obtain ⟨P', hP', hA', hB'⟩ :=
    exists_isIntegralFrobeniusFactor_of_isNormalizedIntegralFraction k₀ X d hAB
  rw [hA'] at hA
  rw [hB'] at hB
  have hPi : P = P' ⟨i, by omega⟩ := hP.unique k₀ X (hP' ⟨i, by omega⟩).2
  have h0 : P.coeff 0 = 1 := hPi ▸ (hP' ⟨i, by omega⟩).1
  have hP0 : P ≠ 0 := fun h ↦ by simp [h] at h0
  -- the complex roots of `P = Pᵢ` are those of `ι P_{i,ℓ}`, of absolute value `q^{-i/2}`
  have hPι : P.map (Int.castRingHom ℂ) = (frobeniusCharpolyRev k₀ l₀ X i).map ι := by
    rw [← hP l₀, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hroot : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots,
      ‖z‖ = (Nat.card k₀ : ℝ) ^ (-(i : ℝ) / 2) := fun z hz ↦ by
    rw [hPι] at hz
    exact (isPureOfWeight_map_frobeniusCharpolyRev k₀ l₀ X d ι i).2 z hz
  have hmon : P.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by rw [h0]; exact one_ne_zero),
      h0]
  have hrev : P.reverse.map (Int.castRingHom ℂ) = (P.map (Int.castRingHom ℂ)).reverse :=
    (Polynomial.reverse_map (RingHom.injective_int _) P).symm
  have hPℂ : P.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP0
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  -- the reciprocal roots have absolute value `q^{i/2}`
  have hrroot : ∀ y ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      ‖y‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2) := fun y hy ↦ by
    rw [hrev, Polynomial.mem_roots_reverse_iff hPℂ] at hy
    have := hroot _ ((Polynomial.mem_roots hPℂ).2 hy.2)
    rw [norm_inv, neg_div, Real.rpow_neg hq.le, inv_inj] at this
    exact this
  -- a reciprocal root `α` of `Pᵢ` is a reciprocal root of `A` or of `B`, hence a Weil number of
  -- some weight `w` of the parity of `i`; its absolute value `q^{i/2}` forces `w = i`
  have hweil : ∀ α ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      IsWeilNumber (Nat.card k₀) i α := fun α hα ↦ by
    have hα' := hα
    rw [hrev, Polynomial.mem_roots_reverse_iff hPℂ] at hα'
    obtain ⟨hα0, hαinv⟩ := hα'
    have key : ∀ s : Finset (Fin (2 * d + 1)), (⟨i, by omega⟩ : Fin (2 * d + 1)) ∈ s →
        α ∈ ((∏ k ∈ s, P' k).reverse.map (Int.castRingHom ℂ)).roots := fun s hs ↦ by
      have hs0 : (∏ k ∈ s, P' k).map (Int.castRingHom ℂ) ≠ 0 := by
        rw [Polynomial.map_prod]
        exact Finset.prod_ne_zero_iff.2 fun k _ ↦
          (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 fun h ↦ by
            have := (hP' k).1
            simp [h] at this
      rw [← Polynomial.reverse_map (RingHom.injective_int _), Polynomial.mem_roots_reverse_iff hs0]
      refine ⟨hα0, ?_⟩
      rw [Polynomial.map_prod, Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hs (by rw [← hPi]; exact hαinv)
    obtain ⟨w, hw⟩ : ∃ w : ℕ, IsWeilNumber (Nat.card k₀) w α := by
      rcases Nat.even_or_odd i with he | ho
      · have hmem : (⟨i, by omega⟩ : Fin (2 * d + 1)) ∈
            Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Even j.1) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
        obtain ⟨w, -, -, hw⟩ := hB α (key _ hmem)
        exact ⟨w, hw⟩
      · have hmem : (⟨i, by omega⟩ : Fin (2 * d + 1)) ∈
            Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Odd j.1) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, ho⟩
        obtain ⟨w, -, -, hw⟩ := hA α (key _ hmem)
        exact ⟨w, hw⟩
    have hq' : 1 < Nat.card k₀ := Finite.one_lt_card
    have hq1 : (Nat.card k₀ : ℝ) ≠ 1 := by exact_mod_cast hq'.ne'
    have hwi : (w : ℝ) / 2 = (i : ℝ) / 2 :=
      (Real.rpow_right_inj hq hq1).1 ((norm_eq_of_isWeilNumber hw).symm.trans (hrroot α hα))
    have hwi' : (w : ℝ) = i := by linarith
    rwa [hwi'] at hw
  refine ⟨fun α hα ↦ ⟨⟨_, hmon, ?_⟩, hweil α hα⟩,
    fun β hβ ↦ isWeilNumber_of_mem_roots hP0 (fun y hy ↦ by rw [hroot y hy, neg_div]) hβ,
    fun l _ _ α hα ↦ ?_⟩
  · rw [show algebraMap ℤ ℂ = Int.castRingHom ℂ from RingHom.ext_int _ _, ← Polynomial.eval_map]
    exact (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hmon.ne_zero)).1 hα
  · rw [← Polynomial.reverse_map (RingHom.injective_int _), hP l, frobeniusCharpolyRev_def,
      FrobeniusModule.localPolynomial,
      (LinearMap.reciprocal_roots_eigenvalues
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd
        (LinearEquiv.isUnit_det' ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobenius)).1] at hα
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (Polynomial.isRoot_of_mem_roots hα)

end Scheme

end AlgebraicGeometry
