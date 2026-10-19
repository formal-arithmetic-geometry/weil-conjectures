/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Sheaf.RingTheory.Depth
import Mathlib.RingTheory.KrullDimension.Regular
import Sheaf.RingTheory.IsRegularOfDimensionDrop

/-!
# Regular sequences and dimension drop in Cohen–Macaulay local rings

Source: Stacks Project, Algebra, Tag 02JN (lemma-reformulate-CM), displayed equivalence
(blueprint: lem-trf-cm-regular-sequence-generator-count).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- A tuple in the maximal ideal of a finite-dimensional Noetherian local ring of depth
at least its dimension is regular exactly when the quotient has the expected dimension.
Source: Stacks Project, Algebra, Tag 02JN, displayed equivalence
(blueprint: lem-trf-cm-regular-sequence-generator-count).

The tuple is represented by a list `xs`, so its length is the nonnegative integer `r`.
The additive equality expresses `dim(R/(xs)) = d - r` with integer subtraction, including
`r > d`; natural-number truncated subtraction would give the wrong criterion.

Proof:
1. If `xs` is regular, apply `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`
   (lem-trf-regular-sequence-dimension-formula), then replace `ringKrullDim R` using `hd`.
   The finite right side rules out bottom and top for the quotient dimension. Writing
   that dimension as a natural `q`, the equality becomes `q + xs.length = d`, hence
   `xs.length ≤ d` and `q = d - xs.length`. For the empty list the quotient is `R`.
2. Conversely, apply `isRegular_of_dimension_drop`
   (lem-weil-pbc-cm-local-dimension-drop-regular-sequence) with `d`, `hd`, `hdepth`,
   `xs`, `hmem`, and the additive dimension equality. These are exactly its hypotheses.
   Thus the empty tuple and all lengths greater than `d` are included in the equivalence.
-/
theorem isRegular_iff_dimension_drop {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := R) R) (xs : List R)
    (hmem : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) :
    IsRegular R xs ↔
      ringKrullDim (R ⧸ Ideal.ofList xs) + (xs.length : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
  sorry

end RingTheory.Sequence
