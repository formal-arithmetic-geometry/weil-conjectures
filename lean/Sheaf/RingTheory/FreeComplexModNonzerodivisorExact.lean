/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Exactness after reduction by a nonzerodivisor

Source: literature/stacks-project/algebra.tex, Lemma Tag 00MZ
(blueprint: lem-weil-pbc-free-complex-mod-nonzerodivisor-exact).
-/

@[expose] public section

universe u

/-- Source: Stacks Project, Algebra, Lemma Tag 00MZ (`lemma-div-x-exact-one-less`).

Given an exact finite free complex over a local ring, reduction modulo a
nonzerodivisor is exact one degree shorter.

Proof following Tag 00MZ, with the node's four steps:
1. Set `F_i = R^(n i)` and reindex as a cochain complex `K^j = F_(e-j)` for
   `0 ≤ j ≤ e`, zero thereafter. The matrix-composition hypothesis gives the
   differential-square-zero condition. In the abelian category of modules
   (`lem-weil-pbc-ring-modules-enough-injectives`), exactness means image equals
   kernel (`def-weil-pbc-exact-sequence`), so `H_i(F) = 0` for `1 ≤ i ≤ e`.
2. Multiplication by `x` commutes with each differential. It is injective on
   each finite free term, coordinate by coordinate, because `x` is a nonzerodivisor
   (`def-weil-pbc-free-module`). Coordinate reduction onto `(R/xR)^(n i)` is
   surjective with kernel `x F_i`; it intertwines the differentials with the
   entrywise reduced matrices (`def-weil-matrix`). Surjectivity also shows the
   reduced matrices form a complex. Thus `0 → K → K → Kbar → 0` is degreewise
   short exact (`def-weil-pbc-exact-sequence`).
3. Apply `lem-weil-pbc-complex-ses-homology-long-exact` in the abelian module
   category. For `2 ≤ i ≤ e`, put `j = e-i`. The exact segment
   `H^j(K) → H^j(Kbar) → H^(j+1)(K)` has zero outer terms by Step 1, hence
   `H^j(Kbar) = 0`.
4. Translate this vanishing back to equality of kernels and images for the
   reduced maps (`def-weil-pbc-exact-sequence`). The underlying sets are the same
   over `R` and `R/xR`. At the leftmost term this says injectivity; at the other
   terms it says exactness for `2 ≤ i < e`. Locality and `x ∈ maximalIdeal R`
   are retained from the source, although its proof does not use them.
The nonzerodivisor hypothesis is Mathlib's `x ∈ nonZeroDivisors R`; in a commutative
ring it says `x * y = 0 → y = 0` (`mem_nonZeroDivisors_iff`).
(blueprint: lem-weil-pbc-free-complex-mod-nonzerodivisor-exact)
-/
theorem free_complex_mod_nonzerodivisor_exact
    (R : Type u) [CommRing R] [IsLocalRing R]
    (e : ℕ) (he : 2 ≤ e) (n : ℕ → ℕ)
    (φ : ∀ i : ℕ, Matrix (Fin (n (i - 1))) (Fin (n i)) R)
    (hcomplex : ∀ i : ℕ, 1 ≤ i → i < e →
      ∀ v : Fin (n (i + 1)) → R,
        (φ i).mulVec ((φ (i + 1)).mulVec v) = 0)
    (hexact : ∀ i : ℕ, 1 ≤ i → i < e →
      Function.Exact (φ (i + 1)).mulVec (φ i).mulVec)
    (hinjective : Function.Injective (φ e).mulVec)
    (x : R) (hxmem : x ∈ IsLocalRing.maximalIdeal R)
    (hx : x ∈ nonZeroDivisors R) :
    let S := R ⧸ Ideal.span ({x} : Set R)
    let q : R →+* S := Ideal.Quotient.mk _
    let φbar : ∀ i : ℕ, Matrix (Fin (n (i - 1))) (Fin (n i)) S :=
      fun i => (φ i).map q
    Function.Injective (φbar e).mulVec ∧
      (∀ i : ℕ, 2 ≤ i → i < e →
        Function.Exact (φbar (i + 1)).mulVec (φbar i).mulVec) := by
  sorry
