/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure

/-!
# A separable closure is the union of its finite separable subextensions

A separable closure of a field `k` is Mathlib's `IsSepClosure k ks`. Here we record that `ks` is
the directed union of its finite separable subextensions, so that `ks` is their filtered colimit.

## Main statements

- `IsSepClosure.exists_intermediateField_mem`: every element of a separable closure lies in a
  finite separable subextension (blueprint `def-pd-separable-closure`).
-/

@[expose] public section

universe u v

open IntermediateField

/-- **A separable closure is the union of its finite separable subextensions.** Let `ks` be a
separable closure of `k`. Every `x ∈ ks` lies in a subextension `K` of `ks/k` that is finite and
separable over `k`, namely `k⟮x⟯`; hence `ks = colim K` over the finite separable subextensions.

The separable closure itself is Mathlib's `IsSepClosure`.

(blueprint: `def-pd-separable-closure`) -/
theorem IsSepClosure.exists_intermediateField_mem (k : Type u) {ks : Type v} [Field k] [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (x : ks) :
    ∃ K : IntermediateField k ks, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧ x ∈ K := by
  have := IsSepClosure.separable (k := k) (K := ks)
  have hx : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  exact ⟨k⟮x⟯, adjoin.finiteDimensional hx.isIntegral,
    (isSeparable_adjoin_simple_iff_isSeparable k ks).mpr hx, mem_adjoin_simple_self k x⟩
