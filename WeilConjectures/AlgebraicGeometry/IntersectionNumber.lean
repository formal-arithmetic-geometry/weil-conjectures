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
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr_coeff` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_zero_of_isZero`: the intersection
  number depends on the coefficient sheaf only through its isomorphism class, and vanishes when
  the coefficient sheaf is zero.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_add_intersectionNumber`:
  **`lem:deg-intersection-additive`**, additivity of the intersection number along a short exact
  sequence of coherent sheaves.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_zero_of_supportDim_lt`:
  **`lem:deg-intersection-small-support`**, the intersection number vanishes when the support of
  `F` has dimension less than `d`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_tensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_zpow`:
  **`thm:deg-intersection-multilinear`**, the intersection number is additive in a line bundle,
  vanishes when a line bundle is the structure sheaf, and is multiplied by `n` when a line bundle
  is replaced by its `n`-th tensor power, for every integer `n`. Together with symmetry this says
  that `(L₁ ⋯ L_d · F)` is a symmetric `ℤ`-multilinear function of the classes of the `Lⱼ` in the
  Picard group of `X`. The three statements are proved for the first line bundle and then
  transported to an arbitrary slot by symmetry, in
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_tensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_zpow`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_const_zpow`:
  **`cor:deg-intersection-powers`**, `((L ^⊗ n) ^ g) = n ^ g · (L ^ g)`.

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

Multilinearity is stated in terms of the sheaves themselves, not of their classes in the Picard
group: there is no `d`-linear map `(Fin d → X.Pic) → ℤ` here. Producing one means choosing a
representative sheaf for a class in `AlgebraicGeometry.Scheme.Pic`, which the skeleton of
`X.Modules` allows but which is a piece of work of its own; the statements below determine such a
map, by `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr`.

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

/-! ### Dependence on the coefficient sheaf -/

/-- **The intersection number depends on the coefficient sheaf only through its isomorphism
class.** -/
lemma intersectionNumber_congr_coeff {F F' : X.Modules} (e : F ≅ F') {d : ℕ}
    (L : Fin d → X.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL = intersectionNumber k F' L hL := by
  simp only [intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  congr 1
  exact eulerChar_congr k (tensorIso e (Iso.refl _))

/-- **The intersection number of a zero coefficient sheaf vanishes.** -/
lemma intersectionNumber_eq_zero_of_isZero {F : X.Modules} (hF : Limits.IsZero F) {d : ℕ}
    (L : Fin d → X.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL = 0 := by
  rw [intersectionNumber]
  refine Finset.sum_eq_zero fun S _ ↦ ?_
  exact mul_eq_zero_of_right _
    (eulerChar_eq_zero_of_isZero k ((invertible_zpowProd L hL _).isZero_tensorObj hF))

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

/-! ### Multilinearity -/

/-- **Reading the intersection number of one family of line bundles off the Snapper function of
another.** Let `K₁, …, K_s` be invertible sheaves of modules and let `v : Fin r → (Fin s → ℤ)` be
an integer matrix such that `⨂ᵢ Kᵢ ^⊗ v j i` has the class of `Lⱼ` in the Picard group of `X` for
every `j`. Then `(L₁ ⋯ L_r · F)` is the composite of the `r` difference operators in the
directions `v 1, …, v r` applied to the Snapper function of `K`, evaluated at `0`.

The point is that the substitution `m ↦ ∑ⱼ mⱼ vⱼ` of integer linear forms carries the Snapper
function of `K` to the Snapper function of `L`, by
`AlgebraicGeometry.Scheme.Modules.eulerChar_tensorZPow_congr`, and that difference operators
transport along it by `fwdDiffComp_comp_addHom`. It is this lemma that lets the three tuples
`(M ⊗ N, L₁, …, L_r)`, `(M, L₁, …, L_r)` and `(N, L₁, …, L_r)` of
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_tensorObj` be compared inside one and
the same Snapper function, that of `(M, N, L₁, …, L_r)`. -/
private lemma intersectionNumber_eq_fwdDiffComp_of_pic (F : X.Modules) {r s : ℕ}
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (K : Fin s → X.Modules) (hK : ∀ j, (K j).Invertible) (v : Fin r → (Fin s → ℤ))
    (hv : ∀ j, ∏ i, Pic.mk (K i) (hK i) ^ v j i = Pic.mk (L j) (hL j)) :
    intersectionNumber k F L hL =
      fwdDiffComp v (fun m ↦ eulerChar k (tensorZPow F K hK m)) 0 := by
  -- the class of the twisting factor `⨂ᵢ Kᵢ ^⊗ cᵢ`, as an additive function of the exponents `c`
  let Φ : (Fin s → ℤ) →+ Additive X.Pic :=
    AddMonoidHom.mk' (fun c ↦ Additive.ofMul (∏ i, Pic.mk (K i) (hK i) ^ c i)) fun c c' ↦ by
      simp only [Pi.add_apply, zpow_add]
      rw [Finset.prod_mul_distrib]
      rfl
  -- the substitution of integer linear forms attached to the matrix `v`
  let φ : (Fin r → ℤ) →ₙ+ (Fin s → ℤ) :=
    AddHom.mk (fun m ↦ ∑ j, m j • v j) fun m m' ↦ by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hφsingle : ∀ j, φ (Pi.single j 1) = v j := fun j ↦ by
    change (∑ i, (Pi.single j (1 : ℤ) : Fin r → ℤ) i • v i) = v j
    rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_smul])
      (fun hb ↦ absurd (Finset.mem_univ _) hb), Pi.single_eq_same, one_smul]
  have hcomp : (fun m ↦ eulerChar k (tensorZPow F K hK m)) ∘ φ =
      fun m ↦ eulerChar k (tensorZPow F L hL m) := by
    funext m
    refine eulerChar_tensorZPow_congr F hK hL ?_
    have h : Φ (φ m) = Additive.ofMul (∏ j, Pic.mk (L j) (hL j) ^ m j) := by
      change Φ (∑ j, m j • v j) = _
      rw [map_sum, ofMul_prod]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Φ.map_zsmul]
      change m j • Additive.ofMul (∏ i, Pic.mk (K i) (hK i) ^ v j i) = _
      rw [hv j, ← ofMul_zpow]
    exact h
  have hveq : (⇑φ ∘ fun j : Fin r ↦ Pi.single j (1 : ℤ)) = v := funext hφsingle
  have hφ0 : φ 0 = 0 := by
    change (∑ j, (0 : Fin r → ℤ) j • v j) = 0
    simp
  rw [intersectionNumber_eq_fwdDiffComp_zero, ← hcomp, fwdDiffComp_comp_addHom, hveq,
    Function.comp_apply, hφ0]

/-- **The intersection number vanishes when one of the line bundles is the structure sheaf**:
`(𝒪ₓ · L₁ ⋯ L_r · F) = 0`.

This is part (2) of `thm:deg-intersection-multilinear` of the blueprint. It needs no hypothesis on
`X`, on `F` or on the `Lⱼ`: the Snapper function of `(𝒪ₓ, L₁, …, L_r)` does not depend on its
first variable, so the first of the `r + 1` difference operators already annihilates it. -/
theorem intersectionNumber_cons_tensorUnit (F : X.Modules) {r : ℕ} (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F (Fin.cons (𝟙_ X.Modules) L)
        (invertible_cons (SheafOfModules.invertible_tensorUnit X.sheaf) hL) = 0 := by
  have hK : ∀ i, ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) i).Invertible :=
    invertible_cons (SheafOfModules.invertible_tensorUnit X.sheaf) hL
  have hprod : ∀ j : Fin (r + 1),
      ∏ i, Pic.mk ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) i) (hK i) ^
          (Pi.single j (1 : ℤ) : Fin (r + 1) → ℤ) i =
        Pic.mk ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) j) (hK j) := fun j ↦ by
    rw [Finset.prod_eq_single j (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero])
      (fun hb ↦ absurd (Finset.mem_univ _) hb), Pi.single_eq_same, zpow_one]
  -- the first direction may be taken to be `0`, since the first factor has trivial class
  have hv : ∀ j : Fin (r + 1),
      ∏ i, Pic.mk ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) i) (hK i) ^
          ((Fin.cons (0 : Fin (r + 1) → ℤ)
            (fun i : Fin r ↦ (Pi.single i.succ 1 : Fin (r + 1) → ℤ)) :
              Fin (r + 1) → Fin (r + 1) → ℤ) j) i =
        Pic.mk ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) j) (hK j) := by
    intro j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      simp
    | succ i =>
      rw [Fin.cons_succ, hprod]
  rw [intersectionNumber_eq_fwdDiffComp_of_pic k F _ hK _ hK _ hv, fwdDiffComp_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show Δ_[(0 : Fin (r + 1) → ℤ)]
      (fun m ↦ eulerChar k (tensorZPow F (Fin.cons (𝟙_ X.Modules) L) hK m)) = 0 from by
    funext y
    simp [fwdDiff]]
  simp

/-! ### Moving a slot to the front -/

/-- Replacing the `j`-th line bundle by `M` and moving it to the front: the intersection number is
unchanged, by symmetry. -/
private lemma intersectionNumber_update_eq_cons (F : X.Modules) {r : ℕ}
    (L : Fin (r + 1) → X.Modules) (hL : ∀ i, (L i).Invertible) (j : Fin (r + 1))
    {M : X.Modules} (hM : M.Invertible) :
    intersectionNumber k F (Function.update L j M) (invertible_update hL hM) =
      intersectionNumber k F (Fin.cons M fun i ↦ L (Equiv.swap 0 j i.succ))
        (invertible_cons hM fun i ↦ hL (Equiv.swap 0 j i.succ)) := by
  rw [← intersectionNumber_comp_perm k F (Function.update L j M) (invertible_update hL hM)
    (Equiv.swap 0 j)]
  refine intersectionNumber_congr k F _ _ fun i ↦ Pic.mk_congr ?_
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero, Function.comp_apply, Equiv.swap_apply_left, Function.update_self]
  | succ i =>
    have hne : Equiv.swap (0 : Fin (r + 1)) j i.succ ≠ j := fun h ↦ Fin.succ_ne_zero i (by
      rw [← Equiv.swap_apply_self (0 : Fin (r + 1)) j i.succ, h, Equiv.swap_apply_right])
    rw [Fin.cons_succ, Function.comp_apply, Function.update_of_ne hne]

/-- Moving the `j`-th line bundle to the front: the intersection number is unchanged, by
symmetry. -/
private lemma intersectionNumber_eq_cons_swap (F : X.Modules) {r : ℕ}
    (L : Fin (r + 1) → X.Modules) (hL : ∀ i, (L i).Invertible) (j : Fin (r + 1))
    {M : X.Modules} (hM : M.Invertible) (hMj : L j = M) :
    intersectionNumber k F L hL =
      intersectionNumber k F (Fin.cons M fun i ↦ L (Equiv.swap 0 j i.succ))
        (invertible_cons hM fun i ↦ hL (Equiv.swap 0 j i.succ)) := by
  rw [← intersectionNumber_comp_perm k F L hL (Equiv.swap 0 j)]
  refine intersectionNumber_congr k F _ _ fun i ↦ Pic.mk_congr ?_
  induction i using Fin.cases with
  | zero => rw [Fin.cons_zero, Function.comp_apply, Equiv.swap_apply_left, hMj]
  | succ i => rw [Fin.cons_succ, Function.comp_apply]

/-- **The intersection number vanishes when any one of the line bundles is the structure sheaf**,
this being part (2) of `thm:deg-intersection-multilinear` of the blueprint in an arbitrary
slot. -/
theorem intersectionNumber_update_tensorUnit (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ i, (L i).Invertible) (j : Fin d) :
    intersectionNumber k F (Function.update L j (𝟙_ X.Modules))
      (invertible_update hL (SheafOfModules.invertible_tensorUnit X.sheaf)) = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos j.pos).symm⟩
  have hu : (𝟙_ X.Modules).Invertible := SheafOfModules.invertible_tensorUnit X.sheaf
  rw [intersectionNumber_update_eq_cons k F L hL j hu]
  exact intersectionNumber_cons_tensorUnit k F _ fun i ↦ hL (Equiv.swap 0 j i.succ)

/-! ### Additivity and homogeneity in the line bundles -/

section Multilinear

variable [Infinite k] [IsProper (X ↘ Spec (.of k))]

/-- **The intersection number is additive in the first line bundle**:

`(M ⊗ N · L₁ ⋯ L_r · F) = (M · L₁ ⋯ L_r · F) + (N · L₁ ⋯ L_r · F)`

for a coherent sheaf `F` with `dim F ≤ r + 1`.

This is part (1) of `thm:deg-intersection-multilinear` of the blueprint. The proof compares the
three intersection numbers inside the Snapper function `Q` of the `(r + 2)`-tuple
`(M, N, L₁, …, L_r)`: they are the composites of the difference operators of `Q` in the directions
`e₀ + e₁`, `e₀` and `e₁` together with `e₂, …, e_{r+1}`, evaluated at `0`, and the operator
identity `Δ_[e₀ + e₁] = Δ_[e₀] + Δ_[e₁] + Δ_[e₀] Δ_[e₁]` of `fwdDiff_add_arg` leaves a remainder
which is a composite of `r + 2` difference operators applied to a numerical polynomial of total
degree at most `r + 1`, hence vanishes. -/
theorem intersectionNumber_cons_tensorObj {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} {M N : X.Modules} (hM : M.Invertible)
    (hN : N.Invertible) (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (hd : F.supportDim ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) :
    intersectionNumber k F (Fin.cons (M ⊗ N) L) (invertible_cons (hM.tensorObj hN) hL) =
      intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) +
        intersectionNumber k F (Fin.cons N L) (invertible_cons hN hL) := by
  obtain ⟨K, hKdef⟩ : ∃ K : Fin (r + 2) → X.Modules, K = Fin.cons M (Fin.cons N L) := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : Fin (r + 2) → ℤ, a = Pi.single 0 1 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : Fin (r + 2) → ℤ, b = Pi.single (0 : Fin (r + 1)).succ 1 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Fin r → (Fin (r + 2) → ℤ), T = fun i ↦ Pi.single i.succ.succ 1 :=
    ⟨_, rfl⟩
  have hK : ∀ i, (K i).Invertible := by
    rw [hKdef]
    exact invertible_cons hM (invertible_cons hN hL)
  have hK0 : K 0 = M := by rw [hKdef, Fin.cons_zero]
  have hK1 : K (0 : Fin (r + 1)).succ = N := by rw [hKdef, Fin.cons_succ, Fin.cons_zero]
  have hK2 : ∀ i : Fin r, K i.succ.succ = L i := fun i ↦ by
    rw [hKdef, Fin.cons_succ, Fin.cons_succ]
  -- the class of the twisting factor attached to a standard basis vector
  have hprod : ∀ j : Fin (r + 2), ∏ i, Pic.mk (K i) (hK i) ^
      (Pi.single j (1 : ℤ) : Fin (r + 2) → ℤ) i = Pic.mk (K j) (hK j) := fun j ↦ by
    rw [Finset.prod_eq_single j (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero])
      (fun hb ↦ absurd (Finset.mem_univ _) hb), Pi.single_eq_same, zpow_one]
  have ha : ∏ i, Pic.mk (K i) (hK i) ^ a i = Pic.mk M hM := by
    rw [hadef, hprod]
    exact Pic.mk_congr hK0
  have hb : ∏ i, Pic.mk (K i) (hK i) ^ b i = Pic.mk N hN := by
    rw [hbdef, hprod]
    exact Pic.mk_congr hK1
  have hT : ∀ i : Fin r, ∏ l, Pic.mk (K l) (hK l) ^ T i l = Pic.mk (L i) (hL i) := fun i ↦ by
    rw [hTdef, hprod]
    exact Pic.mk_congr (hK2 i)
  have hvMN : ∀ j : Fin (r + 1), ∏ i, Pic.mk (K i) (hK i) ^
      ((Fin.cons (a + b) T : Fin (r + 1) → Fin (r + 2) → ℤ) j) i =
      Pic.mk ((Fin.cons (M ⊗ N) L : Fin (r + 1) → X.Modules) j)
        (invertible_cons (hM.tensorObj hN) hL j) := by
    intro j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      simp only [Pi.add_apply, zpow_add]
      rw [Finset.prod_mul_distrib, ha, hb]
      exact (Pic.mk_tensorObj (hM := hM) (hN := hN)).symm.trans (Pic.mk_congr rfl)
    | succ i =>
      rw [Fin.cons_succ, hT]
      simp
  have hvM : ∀ j : Fin (r + 1), ∏ i, Pic.mk (K i) (hK i) ^
      ((Fin.cons a T : Fin (r + 1) → Fin (r + 2) → ℤ) j) i =
      Pic.mk ((Fin.cons M L : Fin (r + 1) → X.Modules) j) (invertible_cons hM hL j) := by
    intro j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, ha]
      simp
    | succ i =>
      rw [Fin.cons_succ, hT]
      simp
  have hvN : ∀ j : Fin (r + 1), ∏ i, Pic.mk (K i) (hK i) ^
      ((Fin.cons b T : Fin (r + 1) → Fin (r + 2) → ℤ) j) i =
      Pic.mk ((Fin.cons N L : Fin (r + 1) → X.Modules) j) (invertible_cons hN hL j) := by
    intro j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, hb]
      simp
    | succ i =>
      rw [Fin.cons_succ, hT]
      simp
  rw [intersectionNumber_eq_fwdDiffComp_of_pic k F _ _ K hK _ hvMN,
    intersectionNumber_eq_fwdDiffComp_of_pic k F _ _ K hK _ hvM,
    intersectionNumber_eq_fwdDiffComp_of_pic k F _ _ K hK _ hvN, fwdDiffComp_cons_add_arg]
  -- the remaining composite of `r + 2` difference operators kills the Snapper function
  have hzero : fwdDiffComp (Fin.cons a (Fin.cons b T))
      (fun m ↦ eulerChar k (tensorZPow F K hK m)) = 0 :=
    (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F K hK (r + 1) hd).fwdDiffComp_eq_zero _
  simp [hzero]

/-- **The intersection number is homogeneous of degree one in the first line bundle**:

`(M ^⊗ n · L₁ ⋯ L_r · F) = n · (M · L₁ ⋯ L_r · F)`

for a coherent sheaf `F` with `dim F ≤ r + 1` and **every** integer `n`, negative included.

This is part (3) of `thm:deg-intersection-multilinear` of the blueprint. Additivity in the first
slot makes `n ↦ (M ^⊗ n · L₁ ⋯ L_r · F)` an additive map `ℤ → ℤ`, because the class of
`M ^⊗ (x + y)` in the Picard group of `X` is that of `M ^⊗ x ⊗ M ^⊗ y`; an additive map on `ℤ` is
multiplication by its value at `1`, which handles the negative exponents at no extra cost. -/
theorem intersectionNumber_cons_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} {M : X.Modules} (hM : M.Invertible)
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (hd : F.supportDim ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (Fin.cons (hM.zpow n) L)
        (invertible_cons (SheafOfModules.invertible_zpow hM n) hL) =
      n * intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) := by
  have hadd : ∀ x y : ℤ,
      intersectionNumber k F (Fin.cons (hM.zpow (x + y)) L)
          (invertible_cons (SheafOfModules.invertible_zpow hM (x + y)) hL) =
        intersectionNumber k F (Fin.cons (hM.zpow x) L)
            (invertible_cons (SheafOfModules.invertible_zpow hM x) hL) +
          intersectionNumber k F (Fin.cons (hM.zpow y) L)
            (invertible_cons (SheafOfModules.invertible_zpow hM y) hL) := by
    intro x y
    have hcongr : intersectionNumber k F (Fin.cons (hM.zpow (x + y)) L)
        (invertible_cons (SheafOfModules.invertible_zpow hM (x + y)) hL) =
        intersectionNumber k F (Fin.cons (hM.zpow x ⊗ hM.zpow y) L)
          (invertible_cons ((SheafOfModules.invertible_zpow hM x).tensorObj
            (SheafOfModules.invertible_zpow hM y)) hL) := by
      refine intersectionNumber_congr k F _ _ fun j ↦ ?_
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        rw [Pic.mk_tensorObj (hM := SheafOfModules.invertible_zpow hM x)
          (hN := SheafOfModules.invertible_zpow hM y), Pic.mk_zpow, Pic.mk_zpow, Pic.mk_zpow,
          zpow_add]
      | succ i => simp
    rw [hcongr]
    exact intersectionNumber_cons_tensorObj k hA hAa F (SheafOfModules.invertible_zpow hM x)
      (SheafOfModules.invertible_zpow hM y) L hL hd
  have h1 : intersectionNumber k F (Fin.cons (hM.zpow 1) L)
      (invertible_cons (SheafOfModules.invertible_zpow hM 1) hL) =
      intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) := by
    refine intersectionNumber_congr k F _ _ fun j ↦ ?_
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp
  have hlin : intersectionNumber k F (Fin.cons (hM.zpow (n • (1 : ℤ))) L)
      (invertible_cons (SheafOfModules.invertible_zpow hM (n • (1 : ℤ))) hL) =
      n • intersectionNumber k F (Fin.cons (hM.zpow 1) L)
        (invertible_cons (SheafOfModules.invertible_zpow hM 1) hL) :=
    (AddMonoidHom.mk' (fun m : ℤ ↦ intersectionNumber k F (Fin.cons (hM.zpow m) L)
      (invertible_cons (SheafOfModules.invertible_zpow hM m) hL)) hadd).map_zsmul n (1 : ℤ)
  simp only [smul_eq_mul, mul_one] at hlin
  rw [hlin, h1]

/-- **The intersection number is additive in each of the line bundles**, this being part (1) of
`thm:deg-intersection-multilinear` of the blueprint in an arbitrary slot. -/
theorem intersectionNumber_update_tensorObj {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ i, (L i).Invertible) (j : Fin d) {M N : X.Modules} (hM : M.Invertible)
    (hN : N.Invertible) (hd : F.supportDim ≤ (d : WithBot ℕ∞)) :
    intersectionNumber k F (Function.update L j (M ⊗ N)) (invertible_update hL (hM.tensorObj hN)) =
      intersectionNumber k F (Function.update L j M) (invertible_update hL hM) +
        intersectionNumber k F (Function.update L j N) (invertible_update hL hN) := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos j.pos).symm⟩
  rw [intersectionNumber_update_eq_cons k F L hL j (hM.tensorObj hN),
    intersectionNumber_update_eq_cons k F L hL j hM,
    intersectionNumber_update_eq_cons k F L hL j hN]
  exact intersectionNumber_cons_tensorObj k hA hAa F hM hN _
    (fun i ↦ hL (Equiv.swap 0 j i.succ)) hd

/-- **Replacing one of the line bundles by its `n`-th tensor power multiplies the intersection
number by `n`**, this being part (3) of `thm:deg-intersection-multilinear` of the blueprint in an
arbitrary slot. -/
theorem intersectionNumber_update_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ i, (L i).Invertible) (j : Fin d) {M : X.Modules} (hM : M.Invertible) (hMj : L j = M)
    (hd : F.supportDim ≤ (d : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (Function.update L j (hM.zpow n))
        (invertible_update hL (SheafOfModules.invertible_zpow hM n)) =
      n * intersectionNumber k F L hL := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos j.pos).symm⟩
  rw [intersectionNumber_update_eq_cons k F L hL j (SheafOfModules.invertible_zpow hM n),
    intersectionNumber_cons_zpow k hA hAa F hM _ (fun i ↦ hL (Equiv.swap 0 j i.succ)) hd n,
    ← intersectionNumber_eq_cons_swap k F L hL j hM hMj]

/-- **Scaling the top self-intersection number**: `((L ^⊗ n) ^ g) = n ^ g · (L ^ g)` for a coherent
sheaf `F` with `dim F ≤ g` and every integer `n`.

This is `cor:deg-intersection-powers` of the blueprint, with the blueprint's hypothesis
`dim X ≤ g` read, as everywhere in this file, as a bound on the dimension of the support of the
coefficient sheaf; taking `F = 𝒪ₓ` gives the statement of the blueprint.

The proof replaces the copies of `L` by copies of `L ^⊗ n` one slot at a time, indexing the slots
already replaced by a finite subset of `Fin g`; each step is
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_zpow` and contributes a factor `n`. -/
theorem intersectionNumber_const_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {g : ℕ} {L : X.Modules} (hL : L.Invertible)
    (hd : F.supportDim ≤ (g : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (fun _ : Fin g ↦ hL.zpow n)
        (fun _ ↦ SheafOfModules.invertible_zpow hL n) =
      n ^ g * intersectionNumber k F (fun _ : Fin g ↦ L) fun _ ↦ hL := by
  classical
  have hite : ∀ (s : Finset (Fin g)) (i : Fin g),
      ((fun i ↦ if i ∈ s then hL.zpow n else L) i).Invertible := fun s i ↦ by
    dsimp only
    split
    · exact SheafOfModules.invertible_zpow hL n
    · exact hL
  have key : ∀ s : Finset (Fin g),
      intersectionNumber k F (fun i ↦ if i ∈ s then hL.zpow n else L) (hite s) =
        n ^ s.card * intersectionNumber k F (fun _ : Fin g ↦ L) fun _ ↦ hL := by
    intro s
    induction s using Finset.induction with
    | empty =>
      rw [Finset.card_empty, pow_zero, one_mul]
      exact intersectionNumber_congr k F _ _ fun i ↦ Pic.mk_congr (by simp)
    | @insert j s hj ih =>
      have hfun : ∀ i, (if i ∈ insert j s then hL.zpow n else L) =
          Function.update (fun i ↦ if i ∈ s then hL.zpow n else L) j (hL.zpow n) i := fun i ↦ by
        rcases eq_or_ne i j with rfl | h
        · rw [Function.update_self, if_pos (Finset.mem_insert_self i s)]
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [intersectionNumber_congr k F (hite (insert j s))
          (invertible_update (hite s) (SheafOfModules.invertible_zpow hL n))
          fun i ↦ Pic.mk_congr (hfun i),
        intersectionNumber_update_zpow k hA hAa F _ (hite s) j hL (by simp [hj]) hd n, ih,
        Finset.card_insert_of_notMem hj, pow_succ, mul_comm (n ^ s.card) n, mul_assoc]
  rw [intersectionNumber_congr k F (fun _ ↦ SheafOfModules.invertible_zpow hL n)
      (hite Finset.univ) fun i ↦ Pic.mk_congr (by simp), key Finset.univ, Finset.card_univ,
    Fintype.card_fin]

end Multilinear

end AlgebraicGeometry.Scheme.Modules
