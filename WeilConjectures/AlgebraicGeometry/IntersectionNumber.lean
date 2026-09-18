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
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_of_supportDim_le`:
  **`lem:deg-intersection-is-top-difference`**, the intersection number is the value at `0` of the
  composite `Δ₁ ⋯ Δ_d` of the `d` standard difference operators applied to the Snapper function
  `m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_d ^⊗ m_d)`, and — once `dim F ≤ d`, so that Snapper's theorem
  makes that composite constant — the value at *any* `m`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr_perm`, with its two special cases
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_comp_perm`:
  **`lem:deg-intersection-symmetric`**, the intersection number depends on `L₁, …, L_d` only
  through the multiset of their classes in the Picard group of `X`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_add_intersectionNumber`:
  **`lem:deg-intersection-additive`**, additivity of the intersection number along a short exact
  sequence of coherent sheaves.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_zero_of_supportDim_lt`:
  **`lem:deg-intersection-small-support`**, the intersection number vanishes when the support of
  `F` has dimension less than `d`.

## Implementation notes

The definition, the unconditional half of `lem:deg-intersection-is-top-difference` and symmetry
are stated with no hypothesis on `X`, on `F` or on the `Lⱼ` beyond invertibility: they are pure
difference calculus and bookkeeping in the Picard group. The results in the `Snapper` section
below consume Snapper's theorem, so they carry its hypotheses — `X` proper over `k` with an ample
invertible sheaf `A`, and `k` infinite, in place of the blueprint's "projective over an
algebraically closed field" — and they inherit the deferrals listed in the `TODO` of
`WeilConjectures.AlgebraicGeometry.Snapper`. See the module docstring of that file.

## TODO

The last sentence of `lem:deg-intersection-is-top-difference` — that `(L₁ ⋯ L_d · F)` is the
coefficient of the monomial `T₁ ⋯ T_d` in the polynomial representing the Snapper function — is
not formalised here. It needs the interaction of `fwdDiffComp` with `MvPolynomial` coefficients,
which is a piece of polynomial algebra of its own.

## References

* S. L. Kleiman, *Toward a numerical theory of ampleness*, Ann. of Math. (2) **84** (1966),
  293–344, §1.
* The blueprint chapter on the degree of an isogeny, section `sec:deg-intersection`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory fwdDiff

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
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_fin_zero`.

This is `def:deg-intersection` of the blueprint. -/
noncomputable def intersectionNumber (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) : ℤ :=
  ∑ S : Finset (Fin d), (-1 : ℤ) ^ (d - S.card) *
    eulerChar k (tensorZPow F L hL fun j ↦ if j ∈ S then 1 else 0)

/-- **The empty intersection number is the Euler characteristic.** -/
@[simp]
lemma intersectionNumber_fin_zero (F : X.Modules) (L : Fin 0 → X.Modules)
    (hL : ∀ j, (L j).Invertible) : intersectionNumber k F L hL = eulerChar k F := by
  rw [intersectionNumber,
    show (Finset.univ : Finset (Finset (Fin 0))) = {∅} from Finset.univ_unique,
    Finset.sum_singleton, Finset.card_empty]
  simpa using eulerChar_congr k (tensorZPowZeroIso F L hL _)

/-! ### The intersection number as a top difference -/

/-- **The intersection number is the top iterated forward difference of the Snapper function**,
evaluated at `0`: applying the `d` standard difference operators `Δ₁, …, Δ_d` to
`m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_d ^⊗ m_d)` and evaluating at `0` gives `(L₁ ⋯ L_d · F)`.

This half of `lem:deg-intersection-is-top-difference` needs no hypothesis on `X`, `F` or the
`Lⱼ`. -/
theorem intersectionNumber_eq_fwdDiffComp_zero (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL =
      fwdDiffComp (fun j ↦ Pi.single j 1) (fun m ↦ eulerChar k (tensorZPow F L hL m)) 0 := by
  -- both sides are alternating sums over the subsets of `Fin d`, by `fwdDiffComp_eq_sum_powerset`
  rw [fwdDiffComp_eq_sum_powerset, intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  -- the twist attached to `S` is the same on both sides: the indicator vector of `S` is the sum
  -- of the standard basis vectors `Pi.single i 1` for `i ∈ S`
  have hS : (∑ i ∈ S, (Pi.single i 1 : Fin d → ℤ)) = fun j ↦ if j ∈ S then 1 else 0 := by
    funext j
    simp
  rw [zsmul_eq_mul, Int.cast_id, zero_add, hS]

/-! ### Symmetry -/

/-- **The intersection number depends on `L₁, …, L_d` only through the multiset of their classes
in the Picard group of `X`**: if some permutation `σ` matches the classes of the `Lⱼ` with those
of the `L'ⱼ`, the two intersection numbers agree.

This is `lem:deg-intersection-symmetric` of the blueprint; its two halves are
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr` and
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_comp_perm` below. -/
theorem intersectionNumber_congr_perm (F : X.Modules) {d : ℕ} {L L' : Fin d → X.Modules}
    (hL : ∀ j, (L j).Invertible) (hL' : ∀ j, (L' j).Invertible) (σ : Equiv.Perm (Fin d))
    (h : ∀ j, Pic.mk (L (σ j)) (hL (σ j)) = Pic.mk (L' j) (hL' j)) :
    intersectionNumber k F L hL = intersectionNumber k F L' hL' := by
  rw [intersectionNumber, intersectionNumber]
  -- `σ` carries the subset indexing a term on the right to the one indexing the equal term on
  -- the left
  refine Fintype.sum_equiv (Equiv.finsetCongr σ.symm) _ _ fun S ↦ ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map]
  congr 1
  refine eulerChar_tensorZPow_congr F hL hL' (Fintype.prod_equiv σ.symm _ _ fun j ↦ ?_)
  rw [← h (σ.symm j), Equiv.apply_symm_apply]
  congr 1
  simp

/-- **The intersection number depends on each `Lⱼ` only through its class in the Picard group of
`X`**, hence, by `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`, only through its isomorphism class.

This is half of `lem:deg-intersection-symmetric` of the blueprint. -/
theorem intersectionNumber_congr (F : X.Modules) {d : ℕ} {L L' : Fin d → X.Modules}
    (hL : ∀ j, (L j).Invertible) (hL' : ∀ j, (L' j).Invertible)
    (h : ∀ j, Pic.mk (L j) (hL j) = Pic.mk (L' j) (hL' j)) :
    intersectionNumber k F L hL = intersectionNumber k F L' hL' :=
  intersectionNumber_congr_perm k F hL hL' (Equiv.refl _) h

/-- **The intersection number is invariant under a permutation of `L₁, …, L_d`.**

This is the other half of `lem:deg-intersection-symmetric` of the blueprint. -/
theorem intersectionNumber_comp_perm (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) (σ : Equiv.Perm (Fin d)) :
    intersectionNumber k F (L ∘ σ) (fun j ↦ hL (σ j)) = intersectionNumber k F L hL :=
  intersectionNumber_congr_perm k F _ hL σ.symm fun _ ↦ Pic.mk_congr (by simp)

/-! ### Additivity in the coefficient sheaf -/

section Additive

variable {C : ShortComplex X.Modules} [IsProper (X ↘ Spec (.of k))]

/-- **The intersection number is additive in the coefficient sheaf** along a short exact sequence

```text
  0 ⟶ C.X₁ ⟶ C.X₂ ⟶ C.X₃ ⟶ 0
```

of coherent sheaves on a scheme proper over a field.

This is `lem:deg-intersection-additive` of the blueprint. -/
theorem intersectionNumber_add_intersectionNumber (hC : C.ShortExact) [C.X₁.IsCoherent]
    [C.X₂.IsCoherent] [C.X₃.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k C.X₁ L hL + intersectionNumber k C.X₃ L hL =
      intersectionNumber k C.X₂ L hL := by
  -- termwise in the defining sum, by additivity of the Euler characteristic along the sequence
  -- twisted by the invertible sheaf `⨂_{i ∈ S} Lᵢ`
  rw [intersectionNumber, intersectionNumber, intersectionNumber, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← mul_add]
  congr 1
  exact eulerChar_tensorObj_add hC (invertible_zpowProd L hL _)

end Additive

/-! ### Snapper's theorem: constancy of the top difference, and vanishing in small dimension -/

section Snapper

variable [Infinite k] [IsProper (X ↘ Spec (.of k))]

/-- **The top iterated forward difference of the Snapper function is constant** once
`dim F ≤ d`, so `(L₁ ⋯ L_d · F)` is its value at *any* `m`, not only at `0`.

This is the second half of `lem:deg-intersection-is-top-difference` of the blueprint; it consumes
Snapper's theorem, so it carries its hypotheses: `X` is proper over the infinite field `k` and
carries an ample invertible sheaf `A`. -/
theorem intersectionNumber_eq_fwdDiffComp_of_supportDim_le {A : X.Modules} (hA : A.Invertible)
    (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) (hd : F.supportDim ≤ (d : WithBot ℕ∞)) (m : Fin d → ℤ) :
    intersectionNumber k F L hL =
      fwdDiffComp (fun j ↦ Pi.single j 1) (fun n ↦ eulerChar k (tensorZPow F L hL n)) m := by
  -- by Snapper's theorem the Snapper function is a numerical polynomial of total degree at most
  -- `dim F ≤ d`, so the composite of the `d` difference operators is constant
  obtain ⟨c, hc⟩ := (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F L hL d
    hd).exists_fwdDiffComp_eq_const fun j ↦ Pi.single j 1
  rw [intersectionNumber_eq_fwdDiffComp_zero k F L hL]
  simp [hc]

/-- **The intersection number vanishes when the support of `F` has dimension less than `d`.**

This is `lem:deg-intersection-small-support` of the blueprint. -/
theorem intersectionNumber_eq_zero_of_supportDim_lt {A : X.Modules} (hA : A.Invertible)
    (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ j, (L j).Invertible) (hd : F.supportDim < (d : WithBot ℕ∞)) :
    intersectionNumber k F L hL = 0 := by
  obtain _ | e := d
  · -- there is nothing below `0` but `⊥`, so `F` is a zero sheaf
    rw [intersectionNumber_fin_zero]
    exact eulerChar_eq_zero_of_isZero k (isZero_of_supportDim_lt_zero F hd)
  · -- by Snapper's theorem the Snapper function is a numerical polynomial of total degree at most
    -- `dim F ≤ d - 1`, so the composite of the `d` difference operators annihilates it
    have hd' : F.supportDim ≤ (e : WithBot ℕ∞) := ENat.WithBot.lt_natCast_add_one_iff.1 hd
    rw [intersectionNumber_eq_fwdDiffComp_zero k F L hL,
      (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F L hL e hd').fwdDiffComp_eq_zero
        fun j ↦ Pi.single j 1]
    simp

end Snapper

end AlgebraicGeometry.Scheme.Modules
