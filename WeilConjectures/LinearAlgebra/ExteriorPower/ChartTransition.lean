/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The change of coordinates of the top differential forms on projective space

Let `δ : R → N` satisfy the Leibniz rule (e.g. the universal derivation into Kähler
differentials). On the overlap of two standard charts `Uₚ`, `U_q` of projective space
`ℙᴰ` (homogeneous coordinates indexed by `Fin (D + 1)`), with affine coordinates
`y k = x_k / x_p` and `z k = x_k / x_q`, we have

`(-1)ᵖ ⋀_{k ≠ p} δ(y k) = (y q)^{D+1} • (-1)^q ⋀_{k ≠ q} δ(z k)`,

the wedge products being taken in increasing order of `k`. This is the computation behind
`ω_ℙ ≅ 𝒪(-D-1)` (blueprint: `lem-pc-projective-space-canonical`).

## Main statements

- `AlternatingMap.map_add_smul_self_of_eq_zero`: adding to every vector a multiple of a fixed
  vector `v m₀` does not change the value of an alternating map.
- `Fin.succAboveSwap`: the permutation of `Fin D` comparing the orders on `Fin (D + 1) \ {p}`
  and `Fin (D + 1) \ {q}` through the transposition of `p` and `q`, and its sign
  `Fin.sign_succAboveSwap`.
- `exteriorPower.ιMulti_chart_transition`: the change of coordinates formula above.
-/

@[expose] public section

open Equiv

namespace AlternatingMap

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Finite ι]

end AlternatingMap

namespace Fin

variable {D : ℕ} {p q : Fin (D + 1)}

end Fin

namespace exteriorPower

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] {D : ℕ}

end exteriorPower
