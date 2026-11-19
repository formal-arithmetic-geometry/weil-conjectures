/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.Rationality
public import WeilConjectures.ZetaFunction.SmoothProper
public import WeilConjectures.ZetaFunction.WeightSeparation
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import WeilConjectures.ZetaLinearAlgebra.Recovery

/-!
# Integral Frobenius factors from the reduced zeta fraction

Let `X₀` be smooth and proper of pure dimension `d` over `k₀ = 𝔽_q`. The zeta series `Z(X₀, T)`
has a unique normalized reduced integral presentation `Z = A / B` (`A, B ∈ ℤ[T]`,
`A(0) = B(0) = 1`, `A` and `B` coprime in `ℚ[T]`), and for every prime `ℓ ≠ p` its scalar
extension is the parity factorization `N_ℓ / D_ℓ` of the determinant factors:
`A^{(ℓ)} = N_ℓ = ∏_{i odd} P_{i,ℓ}` and `B^{(ℓ)} = D_ℓ = ∏_{i even} P_{i,ℓ}`.

Each `P_{i,ℓ}` is universally pure of weight `i` (every reciprocal root has absolute value
`q^{i/2}` under every complex embedding), so the weight-`i` stratum of `A` (`i` odd) or of `B`
(`i` even) — the factor cut out by the roots of absolute value `q^{-i/2}` under every complex
embedding — is defined over `ℚ`, has integer coefficients, and realizes `P_{i,ℓ}` for every
`ℓ ≠ p`. These are the integral Frobenius factors `Pᵢ`: they are constructed here from the
reduced fraction and purity alone, without Poincaré duality and without any connectedness
hypothesis on `X₀`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.existsUnique_isNormalizedIntegralFraction_zetaSeries`: the
  zeta series has a unique normalized reduced integral presentation.
- `AlgebraicGeometry.Scheme.map_eq_frobeniusProduct_of_isNormalizedIntegralFraction`:
  `A^{(ℓ)} = N_ℓ` and `B^{(ℓ)} = D_ℓ`.
- `AlgebraicGeometry.Scheme.exists_isIntegralFrobeniusFactor_of_isNormalizedIntegralFraction`:
  the integral Frobenius factors exist, with `A = ∏_{i odd} Pᵢ` and `B = ∏_{i even} Pᵢ`.
- `AlgebraicGeometry.Scheme.weilRiemannHypothesis_of_isIntegralFrobeniusFactor`: every complex
  root of `Pᵢ` has absolute value `q^{-i/2}`.
- `AlgebraicGeometry.Scheme.zetaSeries_mul_prod_even_eq_prod_odd_of_isIntegralFrobeniusFactor`:
  `Z(X₀, T) · ∏_{i even} Pᵢ = ∏_{i odd} Pᵢ` in `ℚ⟦T⟧`, from the trace formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

/-- There is a prime `ℓ` different from the characteristic of the finite field `k₀`. -/
theorem exists_prime_ne_ringChar (k₀ : Type u) [Field k₀] :
    ∃ l : ℕ, l.Prime ∧ ringChar k₀ ≠ l := by
  by_cases h : ringChar k₀ = 2
  · exact ⟨3, Nat.prime_three, by omega⟩
  · exact ⟨2, Nat.prime_two, h⟩

section General

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- The zeta series of a scheme `X₀` of finite type over a finite field has a unique normalized
reduced integral presentation: there are unique `A, B ∈ ℤ[T]` with `A(0) = B(0) = 1`, `A` and `B`
coprime in `ℚ[T]` and `Z(X₀, T) = A(T) / B(T)`. The series lies in `(1 + T ℤ⟦T⟧) ∩ ℚ(T)`, so
Fatou's lemma applies. -/
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

section ParityProducts

variable {k₀ X d}

omit [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] in
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

omit [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] in
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

end ParityProducts

/-- The normalized reduced integral presentation `Z(X₀, T) = A / B` of the zeta series becomes the
parity factorization `N_ℓ / D_ℓ` after scalar extension to `ℚ̄_ℓ`: `A^{(ℓ)} = N_ℓ` and
`B^{(ℓ)} = D_ℓ`. Both are reduced normalized fractions of `Z(X₀, T)` over `ℚ̄_ℓ`: `A` and `B` remain
coprime after scalar extension, and `N_ℓ`, `D_ℓ` are coprime and have constant coefficient `1`
(`AlgebraicGeometry.Scheme.isCoprime_oddFrobeniusProduct_evenFrobeniusProduct`); a reduced
normalized fraction is unique. -/
theorem map_eq_frobeniusProduct_of_isNormalizedIntegralFraction (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    A.map (Int.castRingHom (PadicAlgCl l)) = oddFrobeniusProduct k₀ l X d ∧
      B.map (Int.castRingHom (PadicAlgCl l)) = evenFrobeniusProduct k₀ l X d := by
  obtain ⟨hA0, hB0, hcop, hZ⟩ := hAB
  have hmap (Q : Polynomial ℤ) : (Q.map (Int.castRingHom ℚ)).map (algebraMap ℚ (PadicAlgCl l)) =
      Q.map (Int.castRingHom (PadicAlgCl l)) := by
    rw [Polynomial.map_map]
    congr 1
  -- the presentation `Z B = A`, read in `ℚ̄_ℓ⟦T⟧`
  have hZℓ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (B.map (Int.castRingHom (PadicAlgCl l)) : PowerSeries (PadicAlgCl l)) =
      (A.map (Int.castRingHom (PadicAlgCl l)) : PowerSeries (PadicAlgCl l)) := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ (PadicAlgCl l))) hZ
    rwa [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, hmap, hmap]
      at h
  -- cross-multiplication against `Z D_ℓ = N_ℓ`: `N_ℓ B^{(ℓ)} = D_ℓ A^{(ℓ)}`
  have hcross : oddFrobeniusProduct k₀ l X d * B.map (Int.castRingHom (PadicAlgCl l)) =
      evenFrobeniusProduct k₀ l X d * A.map (Int.castRingHom (PadicAlgCl l)) := by
    refine Polynomial.coe_injective (PadicAlgCl l) ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← map_zetaSeries_mul_evenFrobeniusProduct k₀ l X d,
      ← hZℓ]
    ring
  have hcop' : IsCoprime (A.map (Int.castRingHom (PadicAlgCl l)))
      (B.map (Int.castRingHom (PadicAlgCl l))) := by
    rw [← hmap, ← hmap]
    exact (Polynomial.isCoprime_map _).2 hcop
  obtain ⟨h1, h2⟩ := Polynomial.eq_of_coeff_zero_eq_one_of_isCoprime
    (by rw [Polynomial.coeff_map, hA0, map_one]) (coeff_zero_oddFrobeniusProduct k₀ l X d) hcop'
    (isCoprime_oddFrobeniusProduct_evenFrobeniusProduct k₀ l X d) hcross
  exact ⟨h1.symm, h2.symm⟩

/-- **Existence of the integral Frobenius factors.** Let `X₀` be smooth and proper of pure
dimension `d` over `k₀ = 𝔽_q` and `Z(X₀, T) = A / B` the normalized reduced integral presentation
of its zeta series. There are `P₀, …, P_{2d} ∈ ℤ[T]` with `Pᵢ(0) = 1` and `Pᵢ^{(ℓ)} = P_{i,ℓ}` for
every prime `ℓ ≠ p`, and `A = ∏_{i odd} Pᵢ`, `B = ∏_{i even} Pᵢ`.

`Pᵢ` is the weight-`i` stratum of `A` (`i` odd) or `B` (`i` even), the factor cut out by the roots
of absolute value `q^{-i/2}` under every complex embedding (`Polynomial.weightFactor`); it is a
normalized integer polynomial (`Polynomial.exists_int_weightFactor_parityPart`) and depends only
on `A`, `B` and `q`. For a prime `ℓ ≠ p` and an embedding `ι : ℚ̄_ℓ → ℂ`, the family `ι P_{i,ℓ}` is
universally pure of weight `i` and its parity products are `ι A^{(ℓ)}` and `ι B^{(ℓ)}`, so
`ι P_{i,ℓ}` is the complexification of this stratum (`Polynomial.eq_map_weightFactor`), and
`Pᵢ^{(ℓ)} = P_{i,ℓ}` since `ι` is injective. -/
theorem exists_isIntegralFrobeniusFactor_of_isNormalizedIntegralFraction {A B : Polynomial ℤ}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      A = ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1), P i ∧
      B = ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1), P i := by
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  -- the weight strata of `A` and `B` are normalized integer polynomials
  choose P hP1 hP2 using fun i : Fin (2 * d + 1) ↦
    Polynomial.exists_int_weightFactor_parityPart hAB.1 hAB.2.1 rfl rfl (Nat.card k₀) i.1
  -- `Pᵢ^{(ℓ)} = P_{i,ℓ}` for every prime `ℓ ≠ p`
  have hfac (i : Fin (2 * d + 1)) : IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i) := by
    intro l _ _
    obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
    obtain ⟨hA, hB⟩ := map_eq_frobeniusProduct_of_isNormalizedIntegralFraction k₀ X d l hAB
    have hmapℂ (C : Polynomial ℤ) : C.map (Int.castRingHom ℂ) =
        (C.map (Int.castRingHom (PadicAlgCl l))).map ι := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    have hmapℚ (C : Polynomial ℤ) :
        (C.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) = C.map (Int.castRingHom ℂ) := by
      rw [Polynomial.map_map, hcast]
    -- the family `ι P_{j,ℓ}` is universally pure of the weights `j`
    have hpure (j : Fin (2 * d + 1)) :
        ((frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι).IsUniversallyPureOfWeight (Nat.card k₀)
          j.1 :=
      isUniversallyPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι (Nat.lt_succ_iff.1 j.isLt)
    -- its parity products are `ι N_ℓ = ι A^{(ℓ)}` and `ι D_ℓ = ι B^{(ℓ)}`
    have hodd : ∏ j ∈ Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Odd j.1),
        (frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι = (oddFrobeniusProduct k₀ l X d).map ι := by
      rw [oddFrobeniusProduct, Polynomial.map_prod, Finset.prod_filter, Finset.prod_filter,
        Finset.prod_range fun i ↦ if Odd i then (frobeniusCharpolyRev k₀ l X i).map ι else 1]
    have heven : ∏ j ∈ Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Even j.1),
        (frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι = (evenFrobeniusProduct k₀ l X d).map ι := by
      rw [evenFrobeniusProduct, Polynomial.map_prod, Finset.prod_filter, Finset.prod_filter,
        Finset.prod_range fun i ↦ if Even i then (frobeniusCharpolyRev k₀ l X i).map ι else 1]
    have hcross : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Odd j.1),
          (frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι) *
            (B.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
        (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * d + 1) ↦ Even j.1),
          (frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι) *
            (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
      rw [hodd, heven, hmapℚ, hmapℚ, hmapℂ A, hmapℂ B, hA, hB]
      exact mul_comm _ _
    -- `ι P_{i,ℓ}` is the complexification of the weight-`i` stratum, i.e. of `Pᵢ`
    have h := Polynomial.eq_map_weightFactor
      (P := fun j : Fin (2 * d + 1) ↦ (frobeniusCharpolyRev k₀ l X (j : ℕ)).map ι) hq hpure
      hAB.2.2.1 (by rw [Polynomial.coeff_map, hAB.1, map_one])
      (by rw [Polynomial.coeff_map, hAB.2.1, map_one]) hcross i
    refine Polynomial.map_injective ι ι.injective ?_
    rw [← hmapℂ, ← hmapℚ, hP2 i, ← h]
  -- the parity products of the `Pᵢ` are `A` and `B`: compare after one scalar extension
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  obtain ⟨hA, hB⟩ := map_eq_frobeniusProduct_of_isNormalizedIntegralFraction k₀ X d l hAB
  have hinj := Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom (PadicAlgCl l)))
  exact ⟨P, fun i ↦ ⟨hP1 i, hfac i⟩,
    hinj (hA.trans (map_prod_odd_eq_oddFrobeniusProduct hfac l).symm),
    hinj (hB.trans (map_prod_even_eq_evenFrobeniusProduct hfac l).symm)⟩

/-- **The Riemann hypothesis for the integral Frobenius factors.** For `X₀` smooth and proper of
pure dimension `d` over `k₀ = 𝔽_q` and integral Frobenius factors `P₀, …, P_{2d}`, every complex
root `z` of `Pᵢ` has absolute value `q^{-i/2}`: the complex roots of `Pᵢ` are those of `ι P_{i,ℓ}`
for any prime `ℓ ≠ p` and embedding `ι : ℚ̄_ℓ → ℂ`, and `ι P_{i,ℓ}` is pure of weight `i`
(`AlgebraicGeometry.Scheme.isPureOfWeight_map_frobeniusCharpolyRev`). -/
theorem weilRiemannHypothesis_of_isIntegralFrobeniusFactor {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    WeilRiemannHypothesis (Nat.card k₀) d P := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  intro i z hz
  have hmap : (P i).map (Int.castRingHom ℂ) = (frobeniusCharpolyRev k₀ l X (i : ℕ)).map ι := by
    rw [← hP i l, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  rw [hmap] at hz
  exact (isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι i).2 z hz

/-- **The zeta function as an alternating product of the integral Frobenius factors.** For `X₀`
smooth and proper of pure dimension `d` over `k₀` and integral Frobenius factors `P₀, …, P_{2d}`,
`Z(X₀, T) · ∏_{i even} Pᵢ(T) = ∏_{i odd} Pᵢ(T)` in `ℚ⟦T⟧`, i.e. `Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`.
This is the trace-to-determinant identity `Z · D_ℓ = N_ℓ` in `ℚ̄_ℓ⟦T⟧`
(`AlgebraicGeometry.Scheme.map_zetaSeries_mul_evenFrobeniusProduct`) for one prime `ℓ ≠ p`,
read back in `ℚ⟦T⟧` through the injective scalar extension. -/
theorem zetaSeries_mul_prod_even_eq_prod_odd_of_isIntegralFrobeniusFactor
    {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
          ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
  obtain ⟨l, hl, hne⟩ := exists_prime_ne_ringChar k₀
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (ringChar k₀ ≠ l) := ⟨hne⟩
  have hc (s : Finset (Fin (2 * d + 1))) :
      ((∏ i ∈ s, P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        ∏ i ∈ s, ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
    rw [Polynomial.map_prod]
    exact map_prod Polynomial.coeToPowerSeries.ringHom _ _
  have hcomp : (algebraMap ℚ (PadicAlgCl l)).comp (Int.castRingHom ℚ) =
      Int.castRingHom (PadicAlgCl l) := RingHom.ext_int _ _
  rw [← hc, ← hc]
  refine PowerSeries.map_injective (algebraMap ℚ (PadicAlgCl l))
    (algebraMap ℚ (PadicAlgCl l)).injective ?_
  rw [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
    Polynomial.map_map, Polynomial.map_map, hcomp, map_prod_even_eq_evenFrobeniusProduct hP l,
    map_prod_odd_eq_oddFrobeniusProduct hP l]
  exact map_zetaSeries_mul_evenFrobeniusProduct k₀ l X d

end Scheme

end AlgebraicGeometry
