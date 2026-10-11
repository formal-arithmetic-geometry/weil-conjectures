/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EulerProduct
public import WeilConjectures.ZetaFunction.BettiSymmetry
public import WeilConjectures.ZetaFunction.DualityReciprocity
public import WeilConjectures.ZetaFunction.Rationality
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import WeilConjectures.ZetaLinearAlgebra.WeilNumbers

/-!
# The Weil conjectures for a smooth proper variety: the five assembled theorems

This file states the five Weil conjectures for a variety over the finite field `k₀ = 𝔽_q` in the
form of the blueprint (subsections `sk-thm-weil1` to `sk-thm-weil5`, nodes
`thm-weil-final-rationality`, `thm-weil-final-integrality`, `thm-weil-final-rh`,
`thm-weil-final-betti`, `thm-weil-final-functional-equation`), and the Riemann hypothesis in
its arithmetic form (`sk-thm-rh`, `prop-arithmetic-roots`).

The inputs are the trace formula, Poincaré duality and the weight estimate; their output is
`AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`. The coefficients of the
zeta series are integral by the Euler product (`AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`,
`AlgebraicGeometry.Scheme.Hom.exists_int_zetaSeries`) while the factorization is `ℓ`-adic by
construction; the two meet in the rationality descent and in the realization independence of the
integral factors (blueprint remarks `rem-zeta-where-this-feeds` and
`rationality-the-criterion-and-the-descent--remark-1`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.weilRationality`: `sk-thm-weil1`, `thm-weil-final-rationality`.
- `AlgebraicGeometry.Scheme.weilIntegralFactors`: `sk-thm-weil2`, `thm-weil-final-integrality`.
- `AlgebraicGeometry.Scheme.riemannHypothesis`: `sk-thm-rh`, `prop-arithmetic-roots`,
  `sk-thm-weil3`, `thm-weil-final-rh`.
- `AlgebraicGeometry.Scheme.weilBetti`: `sk-thm-weil4`, `thm-weil-final-betti`.
- `AlgebraicGeometry.Scheme.weilFunctionalEquation`: `sk-thm-weil5`,
  `thm-weil-final-functional-equation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

namespace Scheme

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `sk-prop-euler` and `prop-euler-product` (closed-point Euler product and
integrality): for a scheme `Y₀` of finite type over a finite field `k`, with `c_r` the number of
closed points of degree `r`,

* only finitely many closed points have degree at most `m`, for every `m`; in particular every
  `c_r` is finite;
* `#Y₀(𝔽_{qⁿ}) = ∑_{r ∣ n} r c_r` for every `n ≥ 1`;
* `Z(Y₀, T) = ∏_{y ∈ |Y₀|} (1 - T^{deg y})⁻¹`, the product converging coefficientwise;
* `Z(Y₀, T) ∈ 1 + T ℤ⟦T⟧`.

The closed points of `Y₀` are its points with finite residue field (`AlgebraicGeometry.Scheme.
finitePoints`). -/
theorem Hom.eulerProduct {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ m : ℕ, {x : X.finitePoints | f.degreeOver x.1 ≤ m}.Finite) ∧
    (∀ n : ℕ, n ≠ 0 → (f.pointCount n : ℕ) =
      ∑ r ∈ n.divisors, r * Nat.card {x : X.finitePoints // f.degreeOver x.1 = r}) ∧
    f.zetaSeries =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ ∧
    ∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries := by
  classical
  refine ⟨f.finite_setOf_degreeOver_le, fun n hn ↦ ?_, f.zetaSeries_eq_tprod,
    (f.exists_int_zetaSeries_and_exists_rat_mul_eq).1⟩
  set T := (f.finite_setOf_degreeOver_le n).toFinset
  have hT : ∀ x : X.finitePoints, f.degreeOver x.1 ∣ n → x ∈ T := fun x hx ↦ by
    simpa [T] using Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx
  rw [f.pointCount_eq_sum hn hT]
  set g : X.finitePoints → ℕ := fun x ↦ f.degreeOver x.1 with hg
  set S : Finset X.finitePoints := T.filter (fun x ↦ g x ∣ n) with hS
  have hmaps : ∀ x ∈ S, g x ∈ n.divisors := fun x hx ↦
    Nat.mem_divisors.2 ⟨(Finset.mem_filter.1 hx).2, hn⟩
  have key : ∑ x ∈ S, g x = ∑ r ∈ n.divisors, ∑ x ∈ S with g x = r, g x :=
    (Finset.sum_fiberwise_of_maps_to hmaps g).symm
  refine key.trans (Finset.sum_congr rfl fun r hr ↦ ?_)
  have hrn : r ∣ n := Nat.dvd_of_mem_divisors hr
  have hc : Nat.card {x : X.finitePoints // f.degreeOver x.1 = r} =
      (S.filter (fun x ↦ g x = r)).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
    simp only [S, g, Finset.mem_filter]
    exact ⟨fun h ↦ ⟨⟨hT x (h ▸ hrn), h ▸ hrn⟩, h⟩, fun h ↦ h.2⟩
  rw [hc, Finset.sum_congr rfl (fun x hx ↦ (Finset.mem_filter.1 hx).2), Finset.sum_const,
    smul_eq_mul, mul_comm]

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `sk-thm-weil1` and `thm-weil-final-rationality` (Weil conjectures I: rationality
and Euler product): for a scheme `X₀` of finite type over a finite field `k`,

* there are `A, B ∈ ℤ[T]` with `B(0) = 1` and `B(T) Z(X₀, T) = A(T)` in `ℚ⟦T⟧`;
* `Z(X₀, T) ∈ 1 + T ℤ⟦T⟧`;
* `Z(X₀, T) = ∏_{x ∈ |X₀|} (1 - T^{deg x})⁻¹`, the product over the closed points. -/
theorem Hom.weilRationality {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    (∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      f.zetaSeries * (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ)) ∧
    (∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries) ∧
    f.zetaSeries =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ :=
  ⟨f.exists_int_mul_zetaSeries_eq, (f.exists_int_zetaSeries_and_exists_rat_mul_eq).1,
    f.zetaSeries_eq_tprod⟩

variable {k₀ : Type u} [Field k₀] [Finite k₀]

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `sk-thm-weil2` and `thm-weil-final-integrality` (Weil conjectures II: integral
Frobenius factors): for `X₀` smooth, proper and geometrically connected of pure dimension `d`,
for every `0 ≤ i ≤ 2d` there is a unique `Pᵢ ∈ ℤ[T]` with `Pᵢ(0) = 1` and
`Pᵢ^{(ℓ)} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for every prime `ℓ ≠ p`, and these satisfy
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}`, independently of `ℓ`. -/
theorem weilIntegralFactors :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i, (P i).coeff 0 = 1 ∧ IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      (∀ (i : Fin (2 * d + 1)) (Q : Polynomial ℤ), Q.coeff 0 = 1 →
        IsIntegralFrobeniusFactor k₀ X (i : ℕ) Q → Q = P i) ∧
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P :=
  by
  obtain ⟨P, hfact, -, -, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  exact ⟨P, fun i ↦ ⟨hfact.coeff_zero_eq_one i, hP i⟩, fun i Q _ hQ ↦ hQ.unique k₀ X (hP i),
    hfact⟩

/-- Blueprint `sk-thm-rh`, `prop-arithmetic-roots`, `sk-thm-weil3` and `thm-weil-final-rh`
(the Riemann hypothesis): for `X₀` smooth, proper and geometrically connected of pure
dimension `d` and an integral Frobenius factor `P` in degree `i ≤ 2d`:

* every reciprocal root `α ∈ ℂ` of `P` (a root of `P^#(U) = U^{deg P} P(U⁻¹)`) is an algebraic
  integer and a `q`-Weil number of weight `i`: `|τ(α)| = q^{i/2}` for every embedding
  `τ : ℚ(α) → ℂ`;
* every ordinary root `β` (a root of `P`) is a `q`-Weil number of weight `-i`;
* for every prime `ℓ ≠ p`, the reciprocal roots of `P` in `ℚ̄_ℓ` are eigenvalues of the
  geometric Frobenius on `Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. -/
theorem riemannHypothesis {i : ℕ} (hi : i ≤ 2 * d) {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) :
    (∀ α ∈ (P.reverse.map (Int.castRingHom ℂ)).roots,
      _root_.IsIntegral ℤ α ∧ IsWeilNumber (Nat.card k₀) i α) ∧
    (∀ β ∈ (P.map (Int.castRingHom ℂ)).roots, IsWeilNumber (Nat.card k₀) (-(i : ℝ)) β) ∧
    ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
      ∀ α ∈ (P.reverse.map (Int.castRingHom (PadicAlgCl l))).roots,
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd.HasEigenvalue α := by
  obtain ⟨P', hfact, -, hrh, hP'⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  have hPi : P = P' ⟨i, by omega⟩ := hP.unique k₀ X (hP' ⟨i, by omega⟩)
  have h0 : P.coeff 0 = 1 := hPi ▸ hfact.coeff_zero_eq_one _
  have hP0 : P ≠ 0 := fun h ↦ by simp [h] at h0
  have hroot : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots,
      ‖z‖ = (Nat.card k₀ : ℝ) ^ (-(i : ℝ) / 2) := hPi ▸ hrh ⟨i, by omega⟩
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
  refine ⟨fun α hα ↦ ⟨⟨_, hmon, ?_⟩, isWeilNumber_of_mem_roots (hmon.ne_zero) hrroot hα⟩,
    fun β hβ ↦ isWeilNumber_of_mem_roots hP0 (fun y hy ↦ by rw [hroot y hy, neg_div]) hβ,
    fun l _ _ α hα ↦ ?_⟩
  · rw [show algebraMap ℤ ℂ = Int.castRingHom ℂ from RingHom.ext_int _ _, ← eval_map]
    exact (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hmon.ne_zero)).1 hα
  · rw [← Polynomial.reverse_map (RingHom.injective_int _), hP l, frobeniusCharpolyRev_def,
      FrobeniusModule.localPolynomial,
      (LinearMap.reciprocal_roots_eigenvalues
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd
        (LinearEquiv.isUnit_det' ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobenius)).1] at hα
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (Polynomial.isRoot_of_mem_roots hα)

/-- Blueprint `sk-thm-weil4` and `thm-weil-final-betti` (Weil conjectures IV: Betti
symmetry): the integral Frobenius factors `Pᵢ` of `X₀` have degrees
`bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T`, `P_{2d} = 1 - qᵈ T`, and the rational function
`Z(X₀, T) = ∏_{i odd} Pᵢ / ∏_{i even} Pᵢ` has a pole of order exactly one at `T = 1` and, if
`d ≥ 1`, at `T = q^{-d}`: the denominator vanishes there to order one and the numerator does
not vanish there (`AlgebraicGeometry.Scheme.bettiSymmetry`). -/
theorem weilBetti :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P ∧
      (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : Fin (2 * d + 1)),
        (P i).natDegree = Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
      (∀ i : Fin (2 * d + 1), (P i.rev).natDegree = (P i).natDegree) ∧
      (P 0).natDegree = 1 ∧ (P (Fin.last (2 * d))).natDegree = 1 ∧
      P 0 = 1 - Polynomial.X ∧
      P (Fin.last (2 * d)) = 1 - C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X ∧
      ((∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
          (P i).map (Int.castRingHom ℚ)).rootMultiplicity 1 = 1 ∧
        ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
          (P i).map (Int.castRingHom ℚ)).IsRoot 1) ∧
      (1 ≤ d →
        (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
          (P i).map (Int.castRingHom ℚ)).rootMultiplicity ((Nat.card k₀ : ℚ) ^ d)⁻¹ = 1 ∧
        ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
          (P i).map (Int.castRingHom ℚ)).IsRoot ((Nat.card k₀ : ℚ) ^ d)⁻¹) := by
  obtain ⟨P, hfact, -, -, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := bettiSymmetry k₀ X d hP
  exact ⟨P, hP, hfact, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Blueprint `sk-thm-weil5` and `thm-weil-final-functional-equation` (Weil conjectures V:
functional equation): for the integral Frobenius factors `Pᵢ` of `X₀`, with
`χ = ∑ᵢ (-1)ⁱ deg Pᵢ` and the determinant constants `Dᵢ = (-1)^{bᵢ} [T^{bᵢ}] Pᵢ`, the factors
satisfy the degreewise reciprocity `P_{2d-i}(q^{-d} t⁻¹) = (-1)^{bᵢ} t^{-bᵢ} Dᵢ⁻¹ Pᵢ(t)` at every
nonzero `t ∈ ℂ`, the number `d χ` is even, `d χ = 2 m`, the sign `ε`
(`AlgebraicGeometry.weilSign`) is `±1`, and the rational function
`Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}` satisfies

`Z(X₀, q^{-d} t⁻¹) = ε q^{m} t^χ Z(X₀, t)`

at every nonzero `t ∈ ℂ` at which no factor vanishes. -/
theorem weilFunctionalEquation :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      (∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) ∧
      (∀ (i : Fin (2 * d + 1)) (t : ℂ), t ≠ 0 →
        ((P i.rev).map (Int.castRingHom ℂ)).eval ((Nat.card k₀ : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
          (-1) ^ (P i).natDegree * t ^ (-((P i).natDegree : ℤ)) *
            (weilDeterminantConstant (P i) : ℂ)⁻¹ * ((P i).map (Int.castRingHom ℂ)).eval t) ∧
      ∃ m : ℤ, (d : ℤ) * Polynomial.alternatingNatDegreeSum P = 2 * m ∧
        (weilSign (Nat.card k₀) m P = 1 ∨ weilSign (Nat.card k₀) m P = -1) ∧
        ∀ t : ℂ, t ≠ 0 → (∀ i, ((P i).map (Int.castRingHom ℂ)).eval t ≠ 0) →
          Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ))
              ((Nat.card k₀ : ℂ) ^ (-(d : ℤ)) * t⁻¹) =
            (weilSign (Nat.card k₀) m P : ℂ) * (Nat.card k₀ : ℂ) ^ m *
              t ^ Polynomial.alternatingNatDegreeSum P *
              Polynomial.alternatingProdEval (fun i ↦ (P i).map (Int.castRingHom ℂ)) t :=
  by
  obtain ⟨P, hfact, hfe, -, hP⟩ := exists_isWeilFactorization_of_smoothProper k₀ X d
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  obtain ⟨hL, -, m, hm⟩ := reciprocity k₀ X d hP
  have hm' : (d : ℤ) * Polynomial.alternatingNatDegreeSum P = 2 * m := by rw [hm]; ring
  exact ⟨P, hP, hL, m, hm', weilSign_eq_one_or_eq_neg_one hq hfact.coeff_zero_eq_one hfe hm',
    fun t ht hne ↦ hfe.alternatingProdEval_eq hq hfact.coeff_zero_eq_one hm' t ht hne⟩

end Scheme

end AlgebraicGeometry
