/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.RealizationIndependence

/-!
# Reciprocal roots of the zeta function

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, and
let `Z(X₀, T) = A / B` be the normalized reduced integral presentation of its zeta series. The
reciprocal roots of `A` and `B` in `ℚ̄` (the roots of the reversed polynomials `A^#`, `B^#`) are
algebraic integers, and each reciprocal root `a` comes with a degree `i`, odd for `A` and even
for `B`, such that `|τ a| = q^{i/2}` for every embedding `τ : ℚ(a) → ℂ` and `θ a` is a Frobenius
eigenvalue on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every embedding `θ : ℚ̄ → ℚ̄_ℓ`.

The degree is that of the integral Frobenius factor `Pᵢ` of which `a` is a reciprocal root: by
`prop-integral-recovery` (`AlgebraicGeometry.Scheme.integral_recovery`), `A = ∏_{i odd} Pᵢ` and
`B = ∏_{i even} Pᵢ`.

## Main statements

- `PowerSeries.IsNormalizedIntegralFraction.isIntegral_of_mem_roots_reverse`: blueprint
  `lemma-reciprocal-roots-zeta--4`.
- `AlgebraicGeometry.Scheme.exists_degree_of_mem_roots_reverse`: blueprint
  `lemma-reciprocal-roots-zeta--5`.
- `AlgebraicGeometry.Scheme.norm_eq_of_hasEigenvalue_of_mem_roots_reverse`: blueprint
  `lemma-reciprocal-roots-zeta--6`.
- `AlgebraicGeometry.Scheme.hasEigenvalue_of_norm_eq_of_mem_roots_reverse`: blueprint
  `lemma-reciprocal-roots-zeta--7`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial IntermediateField

namespace PowerSeries.IsNormalizedIntegralFraction

/-- Blueprint `lemma-reciprocal-roots-zeta--4`: for a normalized reduced integral presentation
`Z = A / B`, every reciprocal root `a ∈ ℚ̄` of `A` or of `B` (a root of `A^#` or `B^#`) is an
algebraic integer, since `A(0) = B(0) = 1` makes `A^#` and `B^#` monic. -/
theorem isIntegral_of_mem_roots_reverse {Z : PowerSeries ℚ} {A B : ℤ[X]}
    (hAB : IsNormalizedIntegralFraction Z A B) {a : AlgebraicClosure ℚ}
    (ha : a ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots ∨
      a ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) :
    IsIntegral ℤ a := by
  have key {C : ℤ[X]} (hC : C.coeff 0 = 1)
      (ha : a ∈ (C.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) : IsIntegral ℤ a :=
    ⟨C.reverse, monic_reverse_of_coeff_zero_eq_one hC, by
      rw [← eval_map]; exact (mem_roots'.1 ha).2⟩
  exact ha.elim (key hAB.1) (key hAB.2.1)

end PowerSeries.IsNormalizedIntegralFraction

namespace Polynomial

/-- A reciprocal root in `ℚ̄` of a finite product of integer polynomials with constant
coefficient `1` is a reciprocal root of one of the factors. -/
theorem exists_mem_roots_reverse_of_mem_roots_reverse_prod {ι : Type*} {s : Finset ι}
    {P : ι → ℤ[X]} (h0 : ∀ i ∈ s, (P i).coeff 0 = 1) {a : AlgebraicClosure ℚ}
    (ha : a ∈ ((∏ i ∈ s, P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) :
    ∃ i ∈ s, a ∈ ((P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
  have hne (i : ι) (hi : i ∈ s) : (P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int).2
      (monic_reverse_of_coeff_zero_eq_one (h0 i hi)).ne_zero
  rw [reverse_prod_of_domain, Polynomial.map_prod,
    roots_prod _ _ (Finset.prod_ne_zero_iff.2 hne), Multiset.mem_bind] at ha
  exact ha

end Polynomial

namespace AlgebraicGeometry

namespace Scheme

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- A reciprocal root `a ∈ ℚ̄` of an integral Frobenius factor `Pᵢ` is mapped by every embedding
`θ : ℚ̄ → ℚ̄_ℓ` to a Frobenius eigenvalue on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`: `θ a` is a reciprocal root of
`Pᵢ^{(ℓ)} = det (1 - T F | Hⁱ)`. -/
theorem hasEigenvalue_of_mem_roots_reverse_of_isIntegralFrobeniusFactor {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℕ} {P : ℤ[X]}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) {a : AlgebraicClosure ℚ}
    (ha : a ∈ (P.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l) :
    ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ a) := by
  set M := (WeilSheaf.adicConstant k₀ l X).cohomology i
  have hroot := (mem_roots'.1 ha).2.map (f := θ)
  rw [Polynomial.map_map, RingHom.ext_int (θ.comp (algebraMap ℤ (AlgebraicClosure ℚ)))
    (Int.castRingHom (PadicAlgCl l)), ← reverse_map (RingHom.injective_int _), hP l,
    frobeniusCharpolyRev_def] at hroot
  have hne : M.localPolynomial ≠ 0 := fun h ↦ by
    simpa [FrobeniusModule.coeff_zero_localPolynomial] using congr(Polynomial.coeff $h 0)
  have h := ((mem_roots_reverse_iff hne).1 ((mem_roots (reverse_eq_zero.not.2 hne)).2 hroot)).2
  have := LinearMap.hasEigenvalue_inv_of_eval_charpolyRev_eq_zero M.frobeniusEnd h
  rwa [inv_inv] at this

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

variable {k₀ X}

/-- The integral Frobenius factors `Pᵢ` of `prop-integral-recovery`, with the Riemann hypothesis,
and the reciprocal roots of the normalized presentation `Z = A / B` distributed among them: a
reciprocal root of `A` is one of some `Pᵢ` with `i` odd, a reciprocal root of `B` one of some
`Pᵢ` with `i` even. -/
theorem exists_integralFrobeniusFactors_of_isNormalizedIntegralFraction {A B : ℤ[X]}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    ∃ P : Fin (2 * d + 1) → ℤ[X],
      (∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      WeilRiemannHypothesis (Nat.card k₀) d P ∧
      (∀ a ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots, ∃ i : Fin (2 * d + 1),
        Odd (i : ℕ) ∧ a ∈ ((P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) ∧
      ∀ a ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots, ∃ i : Fin (2 * d + 1),
        Even (i : ℕ) ∧ a ∈ ((P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
  obtain ⟨-, P, hP, rfl, rfl, -⟩ := integral_recovery k₀ X d hAB
  obtain ⟨-, -, hrh⟩ := isWeilFactorization_of_isIntegralFrobeniusFactor k₀ X d fun i ↦ (hP i).2
  refine ⟨P, hP, hrh, fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  all_goals
    obtain ⟨i, hi, ha⟩ :=
      exists_mem_roots_reverse_of_mem_roots_reverse_prod (fun i _ ↦ (hP i).1) ha
    exact ⟨i, (Finset.mem_filter.1 hi).2, ha⟩


omit [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] in
/-- A reciprocal root `a ∈ ℚ̄` of `A` or `B` lies in exactly the cohomological degree `i` of its
integral Frobenius factor, which has the right parity, satisfies `i ≤ 2d`, `|τ a| = q^{i/2}` for
every `τ : ℚ(a) → ℂ`, and `θ a` is a Frobenius eigenvalue on `Hⁱ` for every `θ : ℚ̄ → ℚ̄_ℓ`. -/
private theorem exists_degree_aux {P : Fin (2 * d + 1) → ℤ[X]}
    (hP : ∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i))
    (hrh : WeilRiemannHypothesis (Nat.card k₀) d P) (i : Fin (2 * d + 1)) {a : AlgebraicClosure ℚ}
    (ha : a ∈ ((P i).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) :
    (∀ τ : ℚ⟮a⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ a)‖ = (Nat.card k₀ : ℝ) ^ ((i : ℕ) / 2 : ℝ)) ∧
      ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l),
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).frobeniusEnd.HasEigenvalue (θ a) :=
  ⟨(isWeilNumber_of_mem_roots (monic_reverse_of_coeff_zero_eq_one (hP i).1).ne_zero
      (fun _ hy ↦ hrh.norm_eq_of_mem_roots_reverse (fun k ↦ (hP k).1) i hy) ha).2,
    fun l _ _ θ ↦ hasEigenvalue_of_mem_roots_reverse_of_isIntegralFrobeniusFactor (hP i).2 ha l θ⟩

/-- Blueprint `lemma-reciprocal-roots-zeta--5` (choice of the degree), with the two clauses
`lemma-reciprocal-roots-zeta--6` and `lemma-reciprocal-roots-zeta--7` for the chosen degree: let
`Z(X₀, T) = A / B` be the normalized reduced integral presentation of the zeta series of `X₀`
smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`. For each
reciprocal root `a ∈ ℚ̄` of `A` (resp. `B`) there is an integer `0 ≤ i ≤ 2d`, odd (resp. even),
such that

* `|τ a| = q^{i/2}` for every field embedding `τ : ℚ(a) → ℂ`, and
* `θ a` is a Frobenius eigenvalue on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p` and every field
  embedding `θ : ℚ̄ → ℚ̄_ℓ`.

The degree `i` is that of the integral Frobenius factor `Pᵢ` of which `a` is a reciprocal root
(`AlgebraicGeometry.Scheme.integral_recovery`). -/
theorem exists_degree_of_mem_roots_reverse {A B : ℤ[X]}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) :
    (∀ a ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots, ∃ i : ℕ, i ≤ 2 * d ∧
      Odd i ∧
      (∀ τ : ℚ⟮a⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ a)‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2)) ∧
      ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l),
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ a)) ∧
    ∀ b ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots, ∃ i : ℕ, i ≤ 2 * d ∧
      Even i ∧
      (∀ τ : ℚ⟮b⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ b)‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2)) ∧
      ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l),
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ b) := by
  obtain ⟨P, hP, hrh, hA, hB⟩ :=
    exists_integralFrobeniusFactors_of_isNormalizedIntegralFraction d hAB
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨i, hi, ha⟩ := hA a ha
    exact ⟨i, by have := i.2; omega, hi, exists_degree_aux d hP hrh i ha⟩
  · obtain ⟨i, hi, hb⟩ := hB b hb
    exact ⟨i, by have := i.2; omega, hi, exists_degree_aux d hP hrh i hb⟩

include d in
/-- Blueprint `lemma-reciprocal-roots-zeta--6` (absolute values): let `a ∈ ℚ̄` be a reciprocal
root of `A` or `B`, where `Z(X₀, T) = A / B` is the normalized reduced integral presentation, and
let `i` be a degree as chosen in `lemma-reciprocal-roots-zeta--5`, i.e. such that `θ a` is a
Frobenius eigenvalue on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for some prime `ℓ ≠ p` and some embedding
`θ : ℚ̄ → ℚ̄_ℓ`. Then `|τ a| = q^{i/2}` for every field embedding `τ : ℚ(a) → ℂ`. -/
theorem norm_eq_of_hasEigenvalue_of_mem_roots_reverse {A B : ℤ[X]}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) {a : AlgebraicClosure ℚ}
    (ha : a ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots ∨
      a ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) {i : ℕ} (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l)
    (hθ : ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ a))
    (τ : ℚ⟮a⟯ →ₐ[ℚ] ℂ) :
    ‖τ (AdjoinSimple.gen ℚ a)‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2) := by
  obtain ⟨P, hP, hrh, hA, hB⟩ :=
    exists_integralFrobeniusFactors_of_isNormalizedIntegralFraction d hAB
  obtain ⟨j, ha⟩ : ∃ j : Fin (2 * d + 1),
      a ∈ ((P j).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
    rcases ha with ha | ha
    · obtain ⟨j, -, ha⟩ := hA a ha; exact ⟨j, ha⟩
    · obtain ⟨j, -, ha⟩ := hB a ha; exact ⟨j, ha⟩
  obtain ⟨hτ, hθ'⟩ := exists_degree_aux d hP hrh j ha
  -- `θ a` is an eigenvalue in degrees `i` and `j`, so purity forces `i = j`
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  have e := (WeilSheaf.isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι i _ hθ).symm.trans
    (WeilSheaf.isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι j _ (hθ' l θ))
  rw [Real.rpow_right_inj (by linarith) hq.ne'] at e
  push_cast at e
  rw [hτ τ, show ((j : ℕ) : ℝ) = i by linarith]

include d in
/-- Blueprint `lemma-reciprocal-roots-zeta--7` (occurrence as an eigenvalue): let `a ∈ ℚ̄` be a
reciprocal root of `A` or `B`, where `Z(X₀, T) = A / B` is the normalized reduced integral
presentation, and let `i` be a degree as chosen in `lemma-reciprocal-roots-zeta--5`, i.e. such
that `|τ a| = q^{i/2}` for every field embedding `τ : ℚ(a) → ℂ`. Then for every prime `ℓ ≠ p` and
every field embedding `θ : ℚ̄ → ℚ̄_ℓ`, `θ a` is a Frobenius eigenvalue on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem hasEigenvalue_of_norm_eq_of_mem_roots_reverse {A B : ℤ[X]}
    (hAB : PowerSeries.IsNormalizedIntegralFraction (X ↘ Spec (CommRingCat.of k₀)).zetaSeries A
      B) {a : AlgebraicClosure ℚ}
    (ha : a ∈ (A.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots ∨
      a ∈ (B.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) {i : ℕ}
    (hi : ∀ τ : ℚ⟮a⟯ →ₐ[ℚ] ℂ, ‖τ (AdjoinSimple.gen ℚ a)‖ = (Nat.card k₀ : ℝ) ^ ((i : ℝ) / 2))
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (θ : AlgebraicClosure ℚ →+* PadicAlgCl l) :
    ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue (θ a) := by
  obtain ⟨P, hP, hrh, hA, hB⟩ :=
    exists_integralFrobeniusFactors_of_isNormalizedIntegralFraction d hAB
  obtain ⟨j, ha'⟩ : ∃ j : Fin (2 * d + 1),
      a ∈ ((P j).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
    rcases ha with ha | ha
    · obtain ⟨j, -, ha⟩ := hA a ha; exact ⟨j, ha⟩
    · obtain ⟨j, -, ha⟩ := hB a ha; exact ⟨j, ha⟩
  obtain ⟨hτ, hθ⟩ := exists_degree_aux d hP hrh j ha'
  -- `a` is a Weil number of weights `i` and `j`, so `i = j`
  have hint : _root_.IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have e := IsWeilNumber.weight_eq Finite.one_lt_card
    (show IsWeilNumber (Nat.card k₀) ((j : ℕ) : ℝ) a from ⟨hint, hτ⟩)
    (show IsWeilNumber (Nat.card k₀) (i : ℝ) a from ⟨hint, hi⟩)
  obtain rfl : (j : ℕ) = i := by exact_mod_cast e
  exact hθ l θ

end Scheme

end AlgebraicGeometry
