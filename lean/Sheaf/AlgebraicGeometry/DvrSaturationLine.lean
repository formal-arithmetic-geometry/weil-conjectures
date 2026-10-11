/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Saturation of a line in a free module over a DVR

Source: Stacks Project, divisors.tex, Tag 0CC4, and the rank-induction paragraph of
`lem-sc-riemann-roch` (blueprint: lem-sc-dvr-saturation-line).
-/

@[expose] public section

open scoped TensorProduct

namespace Module

/-- Source: Stacks Project, divisors.tex, Tag 0CC4, and the rank-induction paragraph of
`lem-sc-riemann-roch` (blueprint: lem-sc-dvr-saturation-line).

The tensor symmetry transports `s` to `K ⊗[R] E`, where Mathlib's standard left `K`-action
is available. The canonical map `i` sends `e` to `1 ⊗ e`, and `L` is the inverse image of
its fraction-field line `V`; since `E` is free, this is the intersection `E ∩ Ks`.

Proof:
1. Clear the finitely many denominators of the coordinates of the nonzero vector `s` in
   the basis `b`. A nonzero multiple belongs to `E`, so `L` is nonzero. It is saturated:
   if `a ≠ 0` and `a • e` belongs to `L`, division by `a` in `K` shows that `e` belongs
   to the same fraction-field line, hence to `L`.
2. Apply `lem-sc-dvr-saturation-line-smith-normal-form` to `L ⊆ E`. Its diagonal bases
   show that the generic rank of `L` is the number of nonzero diagonal factors. The
   denominator-clearing argument and the containment in `V` give `K L = V`. Since
   `s ≠ 0`, this line has dimension one, so `L` is finite free of rank one and its image
   spans `V`.
3. If a diagonal scalar were a nonunit, the corresponding ambient basis vector would
   give a nonzero quotient class killed by that scalar. Saturation from step 1 excludes
   this. Thus every diagonal scalar is a unit, and the remaining `r - 1` basis vectors
   form a basis of `E / L`.
-/
theorem dvr_saturation_line
    {R K E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup E] [Module R E]
    {r : ℕ} (b : Basis (Fin r) R E) (hr : 1 ≤ r)
    (s : E ⊗[R] K) (hs : s ≠ 0) :
    let V : Submodule K (K ⊗[R] E) :=
      Submodule.span K {TensorProduct.comm R E K s}
    let i : E →ₗ[R] K ⊗[R] E := TensorProduct.mk R K E 1
    let L : Submodule R E := (V.restrictScalars R).comap i
    Nonempty (Basis (Fin 1) R L) ∧
      Submodule.span K (i '' (L : Set E)) = V ∧
      Nonempty (Basis (Fin (r - 1)) R (E ⧸ L)) := by
  sorry

end Module
