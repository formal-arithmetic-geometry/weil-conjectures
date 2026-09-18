/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Snapper

/-!
# Intersection numbers

Let `X` be a scheme over a field `k`, let `L₁, …, L_d` be invertible sheaves of `𝒪ₓ`-modules on
`X` and let `F` be a sheaf of `𝒪ₓ`-modules. The *intersection number of `L₁, …, L_d` with
coefficients in `F`* is the alternating sum

`(L₁ ⋯ L_d · F) = ∑_{S ⊆ {1, …, d}} (-1) ^ (d - #S) χ(X, F ⊗ ⨂_{i ∈ S} Lᵢ)`

of Euler characteristics of twists of `F`. This file introduces it and proves its first four
properties.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.intersectionNumber`: the intersection number itself
  (`def:deg-intersection`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_zero` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp`:
  **`lem:deg-intersection-is-top-difference`**, the intersection number is the value at `0` of the
  composite `Δ₁ ⋯ Δ_d` of the `d` standard difference operators applied to the Snapper function
  `m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_d ^⊗ m_d)`, and — once `dim F ≤ d`, so that Snapper's theorem
  makes that composite constant — the value at *any* `m`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_comp_perm`:
  **`lem:deg-intersection-symmetric`**, the intersection number depends on each `Lⱼ` only through
  its isomorphism class, and is invariant under a permutation of the `Lⱼ`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_add_intersectionNumber`:
  **`lem:deg-intersection-additive`**, additivity of the intersection number along a short exact
  sequence of coherent sheaves.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_zero_of_supportDim_lt`:
  **`lem:deg-intersection-small-support`**, the intersection number vanishes when the support of
  `F` has dimension less than `d`.

## Hypotheses

The unconditional half of `lem:deg-intersection-is-top-difference` is pure difference calculus and
is stated with no hypothesis on `X` at all. The two statements that consume Snapper's theorem
carry its hypotheses, which are weaker than the blueprint's "projective over an algebraically
closed field": `X` proper over `k` with an ample invertible sheaf `A`, and `k` infinite. See the
module docstring of `WeilConjectures.AlgebraicGeometry.Snapper`.

## TODO

The last sentence of `lem:deg-intersection-is-top-difference` — that `(L₁ ⋯ L_d · F)` is the
coefficient of the monomial `T₁ ⋯ T_d` in the polynomial representing the Snapper function — is
not formalised here. It needs the interaction of `fwdDiffComp` with `MvPolynomial` coefficients,
which is a piece of polynomial algebra of its own.

Nothing in this file is `\leanok`: everything that consumes Snapper's theorem inherits the
`sorryAx` of the three deliberate deferrals listed in the `TODO` of
`WeilConjectures.AlgebraicGeometry.Snapper`.

## References

The blueprint chapter on the degree of an isogeny, section `sec:deg-intersection`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules fwdDiff

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### The definition -/

/-- **The intersection number `(L₁ ⋯ L_d · F)`** of a family `L₁, …, L_d` of invertible sheaves of
`𝒪ₓ`-modules with coefficients in a sheaf of `𝒪ₓ`-modules `F`, on a scheme `X` over a field `k`:
the alternating sum

`∑_{S ⊆ {1, …, d}} (-1) ^ (d - #S) χ(X, F ⊗ ⨂_{i ∈ S} Lᵢ)`.

The subset `S` enters through its indicator vector, so that the twist `F ⊗ ⨂_{i ∈ S} Lᵢ` is the
sheaf `AlgebraicGeometry.Scheme.Modules.tensorZPow` whose Euler characteristic Snapper's theorem
is about. Taking `F = 𝟙_ X.Modules` gives the intersection number `(L₁ ⋯ L_d)` of the blueprint,
and `d = 0` gives `χ(X, F)` by
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_of_isEmpty`.

This is `def:deg-intersection` of the blueprint. -/
noncomputable def intersectionNumber (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) : ℤ :=
  ∑ S : Finset (Fin d), (-1 : ℤ) ^ (d - S.card) *
    eulerChar k (tensorZPow F L hL fun j ↦ if j ∈ S then 1 else 0)

/-- **The empty intersection number is the Euler characteristic.** -/
@[simp]
lemma intersectionNumber_of_isEmpty (F : X.Modules) (L : Fin 0 → X.Modules)
    (hL : ∀ j, (L j).Invertible) : intersectionNumber k F L hL = eulerChar k F := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  rw [intersectionNumber, huniv, Finset.sum_singleton, Finset.card_empty]
  simpa using eulerChar_congr k (tensorZPowZeroIso F L hL _)

/-! ### The intersection number as a top difference -/

/-- The indicator vector of a subset of `Fin d` is the sum of the corresponding standard basis
vectors of `ℤ ^ d`. -/
private lemma sum_pi_single (d : ℕ) (S : Finset (Fin d)) :
    ∑ i ∈ S, (Pi.single i 1 : Fin d → ℤ) = fun j ↦ if j ∈ S then 1 else 0 := by
  funext j
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

/-- **The intersection number is the top iterated forward difference of the Snapper function**,
evaluated at `0`: applying the `d` standard difference operators `Δ₁, …, Δ_d` to
`m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_d ^⊗ m_d)` and evaluating at `0` gives `(L₁ ⋯ L_d · F)`.

This half of `lem:deg-intersection-is-top-difference` is pure difference calculus: it is the
expansion `fwdDiffComp_eq_sum_powerset` of a composite of difference operators as an alternating
sum over subsets, and needs no hypothesis on `X`, `F` or the `Lⱼ`. -/
theorem intersectionNumber_eq_fwdDiffComp_zero (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL =
      fwdDiffComp (fun j ↦ Pi.single j 1) (fun m ↦ eulerChar k (tensorZPow F L hL m)) 0 := by
  rw [fwdDiffComp_eq_sum_powerset, intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [zsmul_eq_mul, Int.cast_id, zero_add, sum_pi_single]

/-! ### Symmetry -/

/-- Two twists of `F` whose twisting factors have the same class in the Picard group of `X` have
the same Euler characteristic. -/
private lemma eulerChar_tensorZPow_congr (F : X.Modules) {d : ℕ} {L L' : Fin d → X.Modules}
    (hL : ∀ j, (L j).Invertible) (hL' : ∀ j, (L' j).Invertible) {m m' : Fin d → ℤ}
    (h : ∏ j, Pic.mk (L j) (hL j) ^ m j = ∏ j, Pic.mk (L' j) (hL' j) ^ m' j) :
    eulerChar k (tensorZPow F L hL m) = eulerChar k (tensorZPow F L' hL' m') :=
  eulerChar_tensorObj_congr F (invertible_zpowProd L hL m) (invertible_zpowProd L' hL' m')
    (by rw [Pic.mk_zpowProd, Pic.mk_zpowProd]; exact h)

/-- **The intersection number depends on each `Lⱼ` only through its isomorphism class.**

This is half of `lem:deg-intersection-symmetric` of the blueprint. -/
theorem intersectionNumber_congr (F : X.Modules) {d : ℕ} {L L' : Fin d → X.Modules}
    (hL : ∀ j, (L j).Invertible) (hL' : ∀ j, (L' j).Invertible) (e : ∀ j, L j ≅ L' j) :
    intersectionNumber k F L hL = intersectionNumber k F L' hL' := by
  rw [intersectionNumber, intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  congr 1
  exact eulerChar_tensorZPow_congr k F hL hL' (Finset.prod_congr rfl fun j _ ↦
    congrArg (· ^ (if j ∈ S then (1 : ℤ) else 0))
      ((Pic.mk_eq_mk_iff (hM := hL j) (hN := hL' j)).2 ⟨e j⟩))

/-- **The intersection number is invariant under a permutation of `L₁, …, L_d`.**

This is the other half of `lem:deg-intersection-symmetric` of the blueprint. -/
theorem intersectionNumber_comp_perm (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) (σ : Equiv.Perm (Fin d)) :
    intersectionNumber k F (L ∘ σ) (fun j ↦ hL (σ j)) = intersectionNumber k F L hL := by
  rw [intersectionNumber, intersectionNumber]
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S ↦ ?_
  have hcard : (Equiv.finsetCongr σ S).card = S.card := by
    simp [Equiv.finsetCongr]
  rw [hcard]
  congr 1
  refine eulerChar_tensorZPow_congr k F _ hL (Fintype.prod_equiv σ _ _ fun j ↦ ?_)
  congr 1
  simp [Equiv.finsetCongr]

/-! ### Additivity in the coefficient sheaf -/

section Additive

variable {S : ShortComplex X.Modules} [IsProper (X ↘ Spec (.of k))]

/-- The Euler characteristic is additive along a short exact sequence twisted by an invertible
sheaf of modules: tensoring by an invertible sheaf is an equivalence of categories, hence exact. -/
private lemma eulerChar_tensorObj_add (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent]
    [S.X₃.IsCoherent] {N : X.Modules} (hN : N.Invertible) :
    eulerChar k (S.X₁ ⊗ N) + eulerChar k (S.X₃ ⊗ N) = eulerChar k (S.X₂ ⊗ N) := by
  have hEq : (tensorRight N).IsEquivalence := hN.isEquivalence_tensorRight
  have hSE : (S.map (tensorRight N)).ShortExact := hS.map_of_exact (tensorRight N)
  have h₁ : (S.map (tensorRight N)).X₁.IsCoherent := isCoherent_tensorObj_of_invertible S.X₁ hN
  have h₂ : (S.map (tensorRight N)).X₂.IsCoherent := isCoherent_tensorObj_of_invertible S.X₂ hN
  have h₃ : (S.map (tensorRight N)).X₃.IsCoherent := isCoherent_tensorObj_of_invertible S.X₃ hN
  have key := eulerChar_add_eulerChar k hSE
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃] at key
  exact key

/-- **The intersection number is additive in the coefficient sheaf** along a short exact sequence
`0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of coherent sheaves on a scheme proper over a field.

This is `lem:deg-intersection-additive` of the blueprint. -/
theorem intersectionNumber_add_intersectionNumber (hS : S.ShortExact) [S.X₁.IsCoherent]
    [S.X₂.IsCoherent] [S.X₃.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k S.X₁ L hL + intersectionNumber k S.X₃ L hL =
      intersectionNumber k S.X₂ L hL := by
  rw [intersectionNumber, intersectionNumber, intersectionNumber, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [← mul_add]
  congr 1
  exact eulerChar_tensorObj_add k hS (invertible_zpowProd L hL _)

end Additive

/-! ### Snapper's theorem: constancy of the top difference, and vanishing in small dimension -/

section Snapper

variable [Infinite k] [IsProper (X ↘ Spec (.of k))]

/-- **The top iterated forward difference of the Snapper function is constant** once
`dim F ≤ d`, so `(L₁ ⋯ L_d · F)` is its value at *any* `m`, not only at `0`.

This is the second half of `lem:deg-intersection-is-top-difference` of the blueprint; it consumes
Snapper's theorem, so it carries its hypotheses: `X` is proper over the infinite field `k` and
carries an ample invertible sheaf `A`. -/
theorem intersectionNumber_eq_fwdDiffComp {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules) (hL : ∀ j, (L j).Invertible)
    (hd : F.supportDim ≤ (d : WithBot ℕ∞)) (m : Fin d → ℤ) :
    intersectionNumber k F L hL =
      fwdDiffComp (fun j ↦ Pi.single j 1) (fun m ↦ eulerChar k (tensorZPow F L hL m)) m := by
  obtain ⟨c, hc⟩ := (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F L hL d
    hd).exists_fwdDiffComp_eq_const fun j ↦ Pi.single j 1
  rw [intersectionNumber_eq_fwdDiffComp_zero k F L hL, hc]
  rfl

/-- **The intersection number vanishes when the support of `F` has dimension less than `d`.**

This is `lem:deg-intersection-small-support` of the blueprint: by Snapper's theorem the Snapper
function is a numerical polynomial of total degree at most `dim F ≤ d - 1`, so the composite of
`d` difference operators annihilates it. -/
theorem intersectionNumber_eq_zero_of_supportDim_lt {A : X.Modules} (hA : A.Invertible)
    (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) (hd : F.supportDim < (d : WithBot ℕ∞)) :
    intersectionNumber k F L hL = 0 := by
  obtain _ | e := d
  · -- there is nothing below `0` but `⊥`, so `F` is a zero sheaf
    rw [intersectionNumber_of_isEmpty]
    exact eulerChar_eq_zero_of_isZero k ((supportDim_eq_bot_iff F).1
      (ENat.WithBot.lt_natCast_zero_iff.1 hd))
  · have hd' : F.supportDim ≤ (e : WithBot ℕ∞) := ENat.WithBot.lt_natCast_add_one_iff.1 hd
    rw [intersectionNumber_eq_fwdDiffComp_zero k F L hL,
      (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F L hL e hd').fwdDiffComp_eq_zero
        fun j ↦ Pi.single j 1]
    rfl

end Snapper

end AlgebraicGeometry.Scheme.Modules
