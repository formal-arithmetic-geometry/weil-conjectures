/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive roots of unity in a separably closed field

## Main statements

- `IsSepClosed.exists_isPrimitiveRoot`: for `n` invertible in a separably closed field `k`,
  `xⁿ - 1` has `n` distinct roots in `k`, and there is a primitive `n`-th root of unity in `k`
  whose image in every field extension is again primitive.
-/

@[expose] public section

open Polynomial

/-- **Primitive roots of unity.** Let `k` be a separably closed field (for instance an
algebraically closed one) and let `n` be invertible in `k`. Then `xⁿ - 1` has exactly `n`
distinct roots in `k`, and there is a primitive `n`-th root of unity `ζ ∈ k`. Its image in any
field extension `k → K` is again a primitive `n`-th root of unity, which is the compatibility of
the trivialization `θ_ζ` (`IsPrimitiveRoot.zmodAddEquivRootsOfUnity`) with extension of the base
field.
(blueprint: `lem-sc-primitive-root`) -/
theorem IsSepClosed.exists_isPrimitiveRoot (k : Type*) [Field k] [IsSepClosed k] (n : ℕ)
    [NeZero (n : k)] :
    (nthRoots n (1 : k)).Nodup ∧ (nthRootsFinset n (1 : k)).card = n ∧
      ∃ ζ : k, IsPrimitiveRoot ζ n ∧
        ∀ (K : Type*) [Field K] (φ : k →+* K), IsPrimitiveRoot (φ ζ) n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  exact ⟨hζ.nthRoots_one_nodup, hζ.card_nthRootsFinset, ζ, hζ,
    fun K _ φ ↦ hζ.map_of_injective φ.injective⟩
