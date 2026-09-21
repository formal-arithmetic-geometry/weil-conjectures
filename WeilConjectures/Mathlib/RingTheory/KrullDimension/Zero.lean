/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Local rings whose maximal ideal consists of nilpotents are zero-dimensional

## Main results

- `Ring.KrullDimLE.of_maximalIdeal_le_nilradical`: a local ring whose maximal ideal is contained
  in the nilradical has Krull dimension at most `0`.
-/

@[expose] public section

open IsLocalRing

/-- A local ring whose maximal ideal is contained in the nilradical is zero-dimensional. This is
the variant of `Ring.KrullDimLE.of_isMaximal_nilradical` phrased in terms of the maximal ideal.

The converse holds too: it is `(Ring.KrullDimLE.nilradical_eq_maximalIdeal R).ge`. -/
lemma Ring.KrullDimLE.of_maximalIdeal_le_nilradical {R : Type*} [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R ≤ nilradical R) : Ring.KrullDimLE 0 R :=
  have : (nilradical R).IsMaximal :=
    le_antisymm (nilradical_le_prime _) h ▸ maximalIdeal.isMaximal R
  .of_isMaximal_nilradical R
