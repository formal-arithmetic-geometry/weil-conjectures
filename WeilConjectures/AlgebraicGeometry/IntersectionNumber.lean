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

* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_zero`:
  **`lem:deg-intersection-is-top-difference`**, the intersection number is the value at `0` of the
  composite `Δ₁ ⋯ Δ_d` of the `d` standard difference operators applied to the Snapper function
  `m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_d ^⊗ m_d)`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_of_supportDim_le`:
  **`lem:deg-intersection-top-difference-constant`**, that composite is constant once
  `dim F ≤ d`, by Snapper's theorem, so the intersection number is its value at *any* `m`.
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
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq`: the
  second formula of **`lem:deg-intersection-is-top-difference`**, that the intersection numbers of
  all the
  monomials `⨂ᵢ Kᵢ ^⊗ v j i` in a fixed family of line bundles `K₁, …, K_s` are read off one and
  the same Snapper function, that of `K`. This is the engine of the multilinearity results below;
  it generalises `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_zero`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_tensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_zpow`:
  **`thm:deg-intersection-multilinear`** and **`lem:deg-intersection-structure-sheaf`**, the
  intersection number is additive in a line bundle, vanishes when a line bundle is the structure
  sheaf, and is multiplied by `n` when a line bundle is replaced by its `n`-th tensor power, for
  every integer `n`, with the same three statements in an arbitrary slot in
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_tensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_update_zpow`. Their reading as saying that
  `(L₁ ⋯ L_d · F)` is a symmetric `ℤ`-multilinear function of the classes of the `Lⱼ` in the
  Picard group of `X` is not formalised; see the `TODO` below.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_zpow`:
  **`cor:deg-intersection-powers`**, `(L₁ ^⊗ n₁ ⋯ L_g ^⊗ n_g · F) = n₁ ⋯ n_g · (L₁ ⋯ L_g · F)`,
  homogeneity in every slot at once, with `((L ^⊗ n) ^ g) = n ^ g · (L ^ g)` as its constant case
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber_const_zpow`.

## Implementation notes

The definition, `lem:deg-intersection-is-top-difference`, symmetry and
`lem:deg-intersection-structure-sheaf` are stated with no hypothesis on `X`, on `F` or on the
`Lⱼ` beyond invertibility: they are pure difference calculus and bookkeeping in the Picard
group. The results in the `Snapper` section
below consume Snapper's theorem, so they carry its hypotheses — `X` proper over `k` with an ample
invertible sheaf `A`, and `k` infinite, in place of the blueprint's "projective over an
algebraically closed field" — and they inherit the deferrals listed in the `TODO` of
`WeilConjectures.AlgebraicGeometry.Snapper`. See the module docstring of that file.

## TODO

`lem:deg-intersection-top-coefficient` — that `(L₁ ⋯ L_d · F)` is the coefficient of the
monomial `T₁ ⋯ T_d` in the polynomial representing the Snapper function — is not formalised
here. It needs the interaction of `fwdDiffComp` with `MvPolynomial` coefficients, which is a
piece of polynomial algebra of its own.

Multilinearity is stated in terms of the sheaves themselves, not of their classes in the Picard
group: there is no `d`-linear map `(Fin d → X.Pic) → ℤ` here, so the last sentence of
`thm:deg-intersection-multilinear` — that `(L₁ ⋯ L_d · F)` is a symmetric `ℤ`-multilinear
function of the classes of the `Lⱼ` — is not formalised. Producing such a map means choosing a
representative sheaf for a class in `AlgebraicGeometry.Scheme.Pic`, which the skeleton of
`X.Modules` allows but which is a piece of work of its own; the statements below determine the
map uniquely, by `AlgebraicGeometry.Scheme.Modules.intersectionNumber_congr`.

## References

* S. L. Kleiman, *Toward a numerical theory of ampleness*, Ann. of Math. (2) **84** (1966),
  293–344, §1.
* The blueprint chapter on the degree of an isogeny, section `sec:deg-intersection`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SheafOfModules fwdDiff

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

This first half of `lem:deg-intersection-is-top-difference` needs no hypothesis on `X`, `F` or
the `Lⱼ`. -/
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

This is `lem:deg-intersection-top-difference-constant` of the blueprint; it consumes
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

/-! ### Comparing two families of line bundles inside one Snapper function -/

/-- **Reading the intersection number of one family of line bundles off the Snapper function of
another.** Let `K₁, …, K_s` be invertible sheaves of modules and let `v : Fin r → (Fin s → ℤ)` be
an integer matrix such that `⨂ᵢ Kᵢ ^⊗ v j i` has the class of `Lⱼ` in the Picard group of `X` for
every `j`. Then `(L₁ ⋯ L_r · F)` is the composite of the `r` difference operators in the
directions `v 1, …, v r` applied to the Snapper function of `K`, evaluated at `0`.

This is the second formula of `lem:deg-intersection-is-top-difference` of the blueprint — the
statement, Kleiman §1, that all the intersection numbers of monomials in a fixed family of line
bundles are read off one and the same Snapper function. It generalises
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_fwdDiffComp_zero`, which is the case
`K = L`, `v j = Pi.single j 1` and from which it is proved. -/
theorem intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq (F : X.Modules) {r s : ℕ}
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (K : Fin s → X.Modules) (hK : ∀ j, (K j).Invertible) (v : Fin r → (Fin s → ℤ))
    (hv : ∀ j, ∏ i, Pic.mk (K i) (hK i) ^ v j i = Pic.mk (L j) (hL j)) :
    intersectionNumber k F L hL =
      fwdDiffComp v (fun m ↦ eulerChar k (tensorZPow F K hK m)) 0 := by
  -- the substitution `m ↦ ∑ⱼ mⱼ vⱼ` of integer linear forms attached to the matrix `v`
  let φ : (Fin r → ℤ) →ₙ+ (Fin s → ℤ) :=
    AddHom.mk (fun m ↦ ∑ j, m j • v j) fun m m' ↦ by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hφsingle : ∀ j, φ (Pi.single j 1) = v j := fun j ↦ by
    simp only [φ, AddHom.coe_mk]
    rw [Fintype.sum_zsmul_pi_single, one_smul]
  -- it carries the Snapper function of `K` to the Snapper function of `L`, because the
  -- substituted exponent vector names a twisting factor of the same class in the Picard group
  have hcomp : (fun m ↦ eulerChar k (tensorZPow F K hK m)) ∘ φ =
      fun m ↦ eulerChar k (tensorZPow F L hL m) := by
    funext m
    refine eulerChar_tensorZPow_congr F hK hL (Additive.ofMul.injective ?_)
    rw [← Pic.zpowProdHom_apply, ofMul_prod]
    simp only [φ, AddHom.coe_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul (Pic.zpowProdHom K hK), Pic.zpowProdHom_apply, hv j, ← ofMul_zpow]
  -- and difference operators transport along a substitution, by `fwdDiffComp_comp_addHom`
  have hveq : (⇑φ ∘ fun j : Fin r ↦ Pi.single j (1 : ℤ)) = v := funext hφsingle
  have hφ0 : φ 0 = 0 := by simp [φ]
  rw [intersectionNumber_eq_fwdDiffComp_zero, ← hcomp, fwdDiffComp_comp_addHom, hveq,
    Function.comp_apply, hφ0]

/-! ### The structure sheaf -/

/-- **The intersection number vanishes when one of the line bundles is the structure sheaf**:
`(𝒪ₓ · L₁ ⋯ L_r · F) = 0`.

This is `lem:deg-intersection-structure-sheaf` of the blueprint, part (2) of
`thm:deg-intersection-multilinear`. It needs no hypothesis on `X`, on `F` or on the `Lⱼ`. -/
theorem intersectionNumber_cons_tensorUnit (F : X.Modules) {r : ℕ} (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F (Fin.cons (𝟙_ X.Modules) L)
        (invertible_cons (invertible_tensorUnit X.sheaf) hL) = 0 := by
  -- `(𝒪ₓ, L₁, …, L_r)` is presented inside the Snapper function of `(L₁, …, L_r)` by the
  -- exponent matrix whose first row is `0` — the structure sheaf is the empty monomial — and
  -- whose remaining rows are the standard directions
  set v : Fin (r + 1) → (Fin r → ℤ) := Fin.cons 0 fun i ↦ Pi.single i 1 with hvdef
  have hv : ∀ j : Fin (r + 1), ∏ i, Pic.mk (L i) (hL i) ^ v j i =
      Pic.mk ((Fin.cons (𝟙_ X.Modules) L : Fin (r + 1) → X.Modules) j)
        (invertible_cons (invertible_tensorUnit X.sheaf) hL j) := by
    intro j
    rw [hvdef]
    induction j using Fin.cases with
    | zero => simp
    | succ i => simpa using (Fintype.prod_zpow_pi_single _ i 1).trans (zpow_one _)
  -- differencing in the zero direction annihilates the Snapper function
  rw [intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq k F _ _ L hL v hv, fwdDiffComp_succ,
    hvdef]
  simp

/-! ### Moving a slot to the front -/

/-- **Replacing the `j`-th line bundle by `M` and moving it to the front** leaves the intersection
number unchanged, by symmetry. This is the manoeuvre that carries a statement about the first
line bundle to the same statement about an arbitrary one. -/
theorem intersectionNumber_update_eq_cons (F : X.Modules) {r : ℕ}
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

/-- **The intersection number vanishes when any one of the line bundles is the structure sheaf**,
this being `lem:deg-intersection-structure-sheaf` of the blueprint in an arbitrary slot. -/
theorem intersectionNumber_update_tensorUnit (F : X.Modules) {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ i, (L i).Invertible) (j : Fin d) :
    intersectionNumber k F (Function.update L j (𝟙_ X.Modules))
      (invertible_update hL (invertible_tensorUnit X.sheaf)) = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos j.pos).symm⟩
  have hu : (𝟙_ X.Modules).Invertible := invertible_tensorUnit X.sheaf
  rw [intersectionNumber_update_eq_cons k F L hL j hu]
  exact intersectionNumber_cons_tensorUnit k F _ fun i ↦ hL (Equiv.swap 0 j i.succ)

/-! ### Additivity and homogeneity in the line bundles -/

section Multilinear

variable [Infinite k] [IsProper (X ↘ Spec (.of k))]

/-- **The intersection number is additive in the first line bundle**:

`(M ⊗ N · L₁ ⋯ L_r · F) = (M · L₁ ⋯ L_r · F) + (N · L₁ ⋯ L_r · F)`

for a coherent sheaf `F` with `dim F ≤ r + 1`.

This is part (1) of `thm:deg-intersection-multilinear` of the blueprint. -/
theorem intersectionNumber_cons_tensorObj {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} {M N : X.Modules} (hM : M.Invertible)
    (hN : N.Invertible) (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (hd : F.supportDim ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) :
    intersectionNumber k F (Fin.cons (M ⊗ N) L) (invertible_cons (hM.tensorObj hN) hL) =
      intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) +
        intersectionNumber k F (Fin.cons N L) (invertible_cons hN hL) := by
  -- the three intersection numbers are compared inside the Snapper function of the `(r + 2)`-tuple
  -- `K = (M, N, L₁, …, L_r)`, whose exponent vectors are indexed by `0`, `1` and `2, …, r + 1`;
  -- summing the leading direction is what replaces `M` and `N` by `M ⊗ N`, by additivity of the
  -- top difference, `IsNumericalPolynomial.fwdDiffComp_cons_add_arg`
  set K : Fin (r + 2) → X.Modules := Fin.cons M (Fin.cons N L) with hKdef
  set a : Fin (r + 2) → ℤ := Pi.single 0 1 with hadef
  set b : Fin (r + 2) → ℤ := Pi.single (0 : Fin (r + 1)).succ 1 with hbdef
  set T : Fin r → (Fin (r + 2) → ℤ) := fun i ↦ Pi.single i.succ.succ 1 with hTdef
  have hK : ∀ i, (K i).Invertible := by
    rw [hKdef]
    exact invertible_cons hM (invertible_cons hN hL)
  have hK0 : K 0 = M := by rw [hKdef, Fin.cons_zero]
  have hK1 : K (0 : Fin (r + 1)).succ = N := by rw [hKdef, Fin.cons_succ, Fin.cons_zero]
  have hK2 : ∀ i : Fin r, K i.succ.succ = L i := fun i ↦ by
    rw [hKdef, Fin.cons_succ, Fin.cons_succ]
  have hprod : ∀ j : Fin (r + 2), ∏ i, Pic.mk (K i) (hK i) ^
      (Pi.single j (1 : ℤ) : Fin (r + 2) → ℤ) i = Pic.mk (K j) (hK j) := fun j ↦ by
    rw [Fintype.prod_zpow_pi_single, zpow_one]
  have ha : ∏ i, Pic.mk (K i) (hK i) ^ a i = Pic.mk M hM := by
    rw [hadef, hprod]
    exact Pic.mk_congr hK0
  have hb : ∏ i, Pic.mk (K i) (hK i) ^ b i = Pic.mk N hN := by
    rw [hbdef, hprod]
    exact Pic.mk_congr hK1
  have hab : ∏ i, Pic.mk (K i) (hK i) ^ (a + b) i = Pic.mk (M ⊗ N) (hM.tensorObj hN) := by
    simp only [Pi.add_apply, zpow_add]
    rw [Finset.prod_mul_distrib, ha, hb]
    exact (Pic.mk_tensorObj (hM := hM) (hN := hN)).symm
  have hT : ∀ i : Fin r, ∏ l, Pic.mk (K l) (hK l) ^ T i l = Pic.mk (L i) (hL i) := fun i ↦ by
    rw [hTdef, hprod]
    exact Pic.mk_congr (hK2 i)
  -- a line bundle `P` presented by an exponent vector `c` presents `(P, L₁, …, L_r)` by the
  -- exponent matrix whose rows are `c` and `T`
  have hcons : ∀ (c : Fin (r + 2) → ℤ) (P : X.Modules) (hP : P.Invertible),
      ∏ i, Pic.mk (K i) (hK i) ^ c i = Pic.mk P hP →
      ∀ j : Fin (r + 1), ∏ i, Pic.mk (K i) (hK i) ^
          ((Fin.cons c T : Fin (r + 1) → Fin (r + 2) → ℤ) j) i =
        Pic.mk ((Fin.cons P L : Fin (r + 1) → X.Modules) j) (invertible_cons hP hL j) := by
    intro c P hP hc j
    induction j using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, hc]
      simp
    | succ i =>
      rw [Fin.cons_succ, hT]
      simp
  have hvMN := hcons (a + b) (M ⊗ N) (hM.tensorObj hN) hab
  have hvM := hcons a M hM ha
  have hvN := hcons b N hN hb
  rw [intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq k F _ _ K hK _ hvMN,
    intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq k F _ _ K hK _ hvM,
    intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq k F _ _ K hK _ hvN,
    (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F K hK (r + 1)
      hd).fwdDiffComp_cons_add_arg]
  simp

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

/-- **Homogeneity of the intersection number in every slot at once**:

`(L₁ ^⊗ n₁ ⋯ L_g ^⊗ n_g · F) = n₁ ⋯ n_g · (L₁ ⋯ L_g · F)`

for a coherent sheaf `F` with `dim F ≤ g` and every family `n : Fin g → ℤ` of integer exponents,
negative ones included.

This is `cor:deg-intersection-powers` of the blueprint, and part (3) of
`thm:deg-intersection-multilinear` follows from it. -/
theorem intersectionNumber_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {g : ℕ} (L : Fin g → X.Modules) (hL : ∀ i, (L i).Invertible)
    (hd : F.supportDim ≤ (g : WithBot ℕ∞)) (n : Fin g → ℤ) :
    intersectionNumber k F (fun i ↦ (hL i).zpow (n i))
        (fun i ↦ invertible_zpow (hL i) (n i)) =
      (∏ i, n i) * intersectionNumber k F L hL := by
  -- the exponent vector `n j • eⱼ = Pi.single j (n j)` presents `L j ^⊗ n j`, so scaling the `g`
  -- standard directions is what raises the `L j` to their powers; the factor `n₁ ⋯ n_g` then
  -- comes out by homogeneity of the top difference in all its directions at once,
  -- `IsNumericalPolynomial.fwdDiffComp_zsmul_arg`
  have hv : ∀ j, ∏ i, Pic.mk (L i) (hL i) ^ (n j • (Pi.single j 1 : Fin g → ℤ)) i =
      Pic.mk ((hL j).zpow (n j)) (invertible_zpow (hL j) (n j)) := fun j ↦ by
    rw [← Pi.single_smul', smul_eq_mul, mul_one, Fintype.prod_zpow_pi_single, Pic.mk_zpow]
  rw [intersectionNumber_eq_fwdDiffComp_of_prod_zpow_eq k F _ _ L hL _ hv,
    (isNumericalPolynomial_eulerChar_tensorZPow k hA hAa F L hL g hd).fwdDiffComp_zsmul_arg,
    intersectionNumber_eq_fwdDiffComp_zero k F L hL, Pi.smul_apply, smul_eq_mul]

/-- **Scaling the top self-intersection number**: `((L ^⊗ n) ^ g) = n ^ g · (L ^ g)` for a coherent
sheaf `F` with `dim F ≤ g` and every integer `n`.

This is the constant case of `cor:deg-intersection-powers` of the blueprint, with the blueprint's
hypothesis `dim X ≤ g` read, as everywhere in this file, as a bound on the dimension of the
support of the coefficient sheaf; taking `F = 𝒪ₓ` gives the statement of the blueprint. It is the
constant case of `AlgebraicGeometry.Scheme.Modules.intersectionNumber_zpow`. -/
theorem intersectionNumber_const_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {g : ℕ} {L : X.Modules} (hL : L.Invertible)
    (hd : F.supportDim ≤ (g : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (fun _ : Fin g ↦ hL.zpow n) (fun _ ↦ invertible_zpow hL n) =
      n ^ g * intersectionNumber k F (fun _ : Fin g ↦ L) fun _ ↦ hL := by
  simpa using intersectionNumber_zpow k hA hAa F (fun _ : Fin g ↦ L) (fun _ ↦ hL) hd fun _ ↦ n

/-- **The intersection number is homogeneous of degree one in the first line bundle**:

`(M ^⊗ n · L₁ ⋯ L_r · F) = n · (M · L₁ ⋯ L_r · F)`

for a coherent sheaf `F` with `dim F ≤ r + 1` and **every** integer `n`, negative included.

This is part (3) of `thm:deg-intersection-multilinear` of the blueprint. -/
theorem intersectionNumber_cons_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} {M : X.Modules} (hM : M.Invertible)
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible)
    (hd : F.supportDim ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (Fin.cons (hM.zpow n) L) (invertible_cons (invertible_zpow hM n) hL) =
      n * intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) := by
  -- the exponent family `(n, 1, …, 1)` scales the first slot and leaves the others alone
  have h := intersectionNumber_zpow k hA hAa F (Fin.cons M L) (invertible_cons hM hL) hd
    (Fin.cons n fun _ ↦ 1)
  rw [Fin.prod_cons, Finset.prod_const_one, mul_one] at h
  rw [← h]
  refine intersectionNumber_congr k F _ _ fun j ↦ ?_
  induction j using Fin.cases with
  | zero => simp [Pic.mk_zpow]
  | succ i => simp [Pic.mk_zpow]

/-- **Replacing one of the line bundles by the `n`-th tensor power of a line bundle `M`
multiplies the intersection number by `n`**, this being part (3) of
`thm:deg-intersection-multilinear` of the blueprint in an arbitrary slot. -/
theorem intersectionNumber_update_zpow {A : X.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    (F : X.Modules) [F.IsCoherent] {d : ℕ} (L : Fin d → X.Modules)
    (hL : ∀ i, (L i).Invertible) (j : Fin d) {M : X.Modules} (hM : M.Invertible)
    (hd : F.supportDim ≤ (d : WithBot ℕ∞)) (n : ℤ) :
    intersectionNumber k F (Function.update L j (hM.zpow n))
        (invertible_update hL (invertible_zpow hM n)) =
      n * intersectionNumber k F (Function.update L j M) (invertible_update hL hM) := by
  -- the exponent family concentrated at `j` scales that slot only, so no slot has to be moved
  -- into position
  have h := intersectionNumber_zpow k hA hAa F (Function.update L j M) (invertible_update hL hM)
    hd (Function.update (fun _ ↦ (1 : ℤ)) j n)
  rw [Finset.prod_update_of_mem (Finset.mem_univ j), Finset.prod_const_one, mul_one] at h
  rw [← h]
  refine intersectionNumber_congr k F _ _ fun i ↦ ?_
  rcases eq_or_ne i j with rfl | hne
  · simp [Pic.mk_zpow]
  · simp [Function.update_of_ne hne, Pic.mk_zpow]

end Multilinear

end AlgebraicGeometry.Scheme.Modules
