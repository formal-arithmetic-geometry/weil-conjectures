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

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`.
The zeta series `Z(X₀, T)` has a unique normalized reduced integral presentation `Z = A / B`
(`A, B ∈ ℤ[T]`, `A(0) = B(0) = 1`, `A` and `B` coprime in `ℚ[T]`). This file identifies it with
the parity products of the integral Frobenius factors `Pᵢ`, `A = ∏_{i odd} Pᵢ` and
`B = ∏_{i even} Pᵢ`, so that `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ` for every `ℓ ≠ p`; and it recovers
each `Pᵢ` from `A` and `B` alone, without reference to `ℓ`: `Pᵢ` is the stratum polynomial
`Qᵢ = ∏ (1 - α T)`, the product over the reciprocal roots `α` of `A` (`i` odd) or `B` (`i` even)
which are `q`-Weil numbers of weight `i`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.existsUnique_isNormalizedIntegralFraction_zetaSeries`: the
  zeta series has a unique normalized reduced integral presentation
  (`prop-weil-zeta-normalized-presentation`).
- `AlgebraicGeometry.Scheme.integral_recovery`: the integral Frobenius factors and the
  identification of the normalized presentation with their parity products
  (`prop-integral-recovery`).
- `AlgebraicGeometry.Scheme.realization_independence`: the stratum polynomials `Qᵢ` of the
  normalized presentation are integral, and their scalar extension along every `ℓ`-adic
  realization `ℚ̄ ≃ ℚ̄^{(ℓ)} ⊆ ℚ̄_ℓ` is `P_{i,ℓ}` (`thm-weil-realization-independence`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

section General

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Blueprint `prop-weil-zeta-normalized-presentation`: the zeta series of a scheme `X₀` of finite
type over a finite field has a unique normalized reduced integral presentation: there are unique
`A, B ∈ ℤ[T]` with `A(0) = B(0) = 1`, `A` and `B` coprime in `ℚ[T]` and `Z(X₀, T) = A(T) / B(T)`.
The series lies in `(1 + T ℤ⟦T⟧) ∩ ℚ(T)` (`prop-weil-zeta-integral-rational`), so Fatou's lemma
(`prop-weil-integral-rational-series`) applies. -/
theorem Hom.existsUnique_isNormalizedIntegralFraction_zetaSeries (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃! p : ℤ[X] × ℤ[X], PowerSeries.IsNormalizedIntegralFraction f.zetaSeries p.1 p.2 := by
  obtain ⟨⟨Z, hZ0, hZ⟩, hrat⟩ := f.exists_int_zetaSeries_and_exists_rat_mul_eq
  rw [← hZ] at hrat ⊢
  exact PowerSeries.existsUnique_isNormalizedIntegralFraction Z hZ0 hrat

end General

variable {k₀ : Type u} [Field k₀] [Finite k₀]

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

section ParityProducts

variable {k₀ X d}

omit [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- The scalar extension of the odd product `∏_{i odd} Pᵢ` of the integral Frobenius factors is
the parity product `N_ℓ = ∏_{i odd} P_{i,ℓ}`. -/
theorem map_prod_odd_eq_oddFrobeniusProduct {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P i).map
        (Int.castRingHom (PadicAlgCl l)) = oddFrobeniusProduct k₀ l X d := by
  rw [Polynomial.map_prod, oddFrobeniusProduct, Finset.prod_filter, Finset.prod_filter,
    Finset.prod_range fun i ↦ if Odd i then frobeniusCharpolyRev k₀ l X i else 1]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [hP i l]

omit [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- The scalar extension of the even product `∏_{i even} Pᵢ` of the integral Frobenius factors
is the parity product `D_ℓ = ∏_{i even} P_{i,ℓ}`. -/
theorem map_prod_even_eq_evenFrobeniusProduct {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P i).map
        (Int.castRingHom (PadicAlgCl l)) = evenFrobeniusProduct k₀ l X d := by
  rw [Polynomial.map_prod, evenFrobeniusProduct, Finset.prod_filter, Finset.prod_filter,
    Finset.prod_range fun i ↦ if Even i then frobeniusCharpolyRev k₀ l X i else 1]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [hP i l]

/-- The parity products `∏_{i odd} Pᵢ` and `∏_{i even} Pᵢ` of the integral Frobenius factors are
a normalized reduced integral presentation of `Z(X₀, T)`: their constant coefficients are `1`,
they factor the zeta series, and they are coprime in `ℚ[T]` since their scalar extensions
`N_ℓ`, `D_ℓ` are coprime (`prop-weight-separation`). -/
theorem isNormalizedIntegralFraction_prod {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P i)
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P i) := by
  obtain ⟨hfact, -, -⟩ := isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d hP
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  have hmap (Q : Polynomial ℤ) : (Q.map (Int.castRingHom ℚ)).map (algebraMap ℚ (PadicAlgCl l)) =
      Q.map (Int.castRingHom (PadicAlgCl l)) := by
    rw [Polynomial.map_map]
    congr 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_zero_prod]
    exact Finset.prod_eq_one fun i _ ↦ hfact.coeff_zero_eq_one i
  · rw [coeff_zero_prod]
    exact Finset.prod_eq_one fun i _ ↦ hfact.coeff_zero_eq_one i
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
    exact hfact.factorization

end ParityProducts

/-- Blueprint `prop-integral-recovery` (integral recovery): for `X₀` smooth, proper and
geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, and `Z(X₀, T) = A / B` the
normalized reduced integral presentation of its zeta series:

* for every `0 ≤ i ≤ 2d` there is a unique `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1` and
  `Pᵢ^{(ℓ)} = P_{i,ℓ}` for every prime `ℓ ≠ p` (the integral Frobenius factors);
* `A = ∏_{i odd} Pᵢ` and `B = ∏_{i even} Pᵢ`, hence `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ` for every
  `ℓ ≠ p`;
* `Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`;
* `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`.

The normalized presentation is unique (`prop-weil-zeta-normalized-presentation`), and the parity
products of the `Pᵢ` are one (`AlgebraicGeometry.Scheme.isNormalizedIntegralFraction_prod`). -/
theorem integral_recovery {A B : Polynomial ℤ}
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

/-- Blueprint `thm-weil-realization-independence` (realization independence of the integral
factors): for `X₀` smooth, proper and geometrically connected of pure dimension `d` over
`k₀ = 𝔽_q`, `Z(X₀, T) = A / B` the normalized reduced integral presentation of its zeta series
and `0 ≤ i ≤ 2d`, let `Qᵢ = ∏_{α ∈ Rᵢ} (1 - α T)` be the stratum polynomial of the multiset `Rᵢ`
of reciprocal roots in `ℚ̄` of `A` (`i` odd) or `B` (`i` even) which are `q`-Weil numbers of
weight `i` (`Polynomial.weilStratumPoly`). Then

* `Qᵢ` has integer coefficients and `Qᵢ(0) = 1`;
* for every prime `ℓ ≠ p` and every `ℓ`-adic realization `ρ : ℚ̄ ≃ ℚ̄^{(ℓ)} ⊆ ℚ̄_ℓ`
  (`AlgebraicRealization`), the scalar extension of `Qᵢ` along `ρ` is `P_{i,ℓ}`;
* `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ`.

By `prop-integral-recovery`, `A` and `B` are the parity products of the integral Frobenius factors
`Pⱼ`, whose reciprocal roots are `q`-Weil numbers of weight `j` (`sk-thm-rh`); so the weight-`i`
stratum of `A` or `B` is the reciprocal-root multiset of `Pᵢ` (`Polynomial.weilStratum_prod`),
and `Qᵢ = Pᵢ`. -/
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
  obtain ⟨-, P, hP, rfl, rfl, hNB, hfact, -⟩ := integral_recovery k₀ X d hAB
  obtain ⟨-, -, hrh⟩ := isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d fun i ↦ (hP i).2
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
  refine ⟨⟨P j, (hP j).1, hQ.symm⟩, fun l _ _ ρ ↦ ?_, hNB⟩
  rw [hQ, Polynomial.map_map, ← (hP j).2 l]
  congr 1
  exact RingHom.ext_int _ _

end Scheme

end AlgebraicGeometry
