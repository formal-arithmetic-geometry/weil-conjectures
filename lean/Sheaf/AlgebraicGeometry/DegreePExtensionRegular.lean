/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Regularity of a degree-p polynomial extension

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07PG
(blueprint: lem-weil-pbc-degree-p-extension-regular)
-/

@[expose] public section

universe u

namespace Algebra

/-- (blueprint: lem-weil-pbc-degree-p-extension-regular)
Let `R` be a regular commutative ring, `f : R`, and `D` a derivation of `R`
with `D f` a unit.  For every positive natural number `n`, adjoining an
`n`-th root of `f` preserves regularity.  This is the statement of Stacks
Project, More on Algebra, Lemma 07PG (first sentence).

Proof (the node's four steps):
1. Extend `D` coefficientwise to `R[X]`, sending `X` to zero
   (`def-weil-polynomial-ring`). Additivity holds coefficientwise; applying
   the Leibniz rule to each coefficient of a product proves the extended
   map is a derivation, agreeing with `D` on constants.
2. The Leibniz rule gives `D 1 = 0`, and additivity gives `D 0 = 0`.
   Thus the extension annihilates `X ^ n` and sends `X ^ n - C f` to
   `-C (D f)`. This constant is a unit because `D f` is a unit; its image
   in the quotient remains a unit (`def-weil-polynomial-ring`).
3. The polynomial ring is smooth over `R`
   (`lem-weil-pbc-polynomial-ring-smooth`, with one variable). Regularity
   ascends along smooth maps (`lem-weil-pbc-regular-ring-smooth-ascent`,
   Stacks 07NF), so `R[X]` is regular (`def-weil-regular-scheme`).
4. Apply `lem-weil-pbc-hypersurface-derivation-regular` (Stacks 07PF) to
   this regular ring, the element `X ^ n - C f`, and the extended
   derivation. Step 2 verifies its unit hypothesis in the quotient,
   yielding regularity of the stated quotient for every `n ≥ 1`.
-/
theorem isRegularRing_quotient_X_pow_sub_of_isUnit_derivation
    (R : Type u) [CommRing R] [IsRegularRing R]
    (f : R) (D : Derivation ℤ R R) (hDf : IsUnit (D f))
    (n : ℕ) (hn : 1 ≤ n) :
    IsRegularRing
      (Polynomial R ⧸ Ideal.span ({Polynomial.X ^ n - Polynomial.C f} : Set (Polynomial R))) := by
  sorry

end Algebra
