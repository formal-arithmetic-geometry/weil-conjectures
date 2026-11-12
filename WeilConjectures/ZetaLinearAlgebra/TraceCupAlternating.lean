/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import WeilConjectures.ZetaLinearAlgebra.TraceCup

/-!
# The middle-degree trace–cup pairing in odd dimension is alternating

For a trace–cup structure of degree `n = 2d` on a graded family of Frobenius modules over a
field `K` of characteristic different from `2`, graded commutativity gives
`⟨x, y⟩ = (-1)^{d·d} ⟨y, x⟩` on `H^d`. If `d` is odd, the pairing is therefore alternating:
`⟨x, x⟩ = -⟨x, x⟩`, hence `⟨x, x⟩ = 0`.

## Main statements

- `FrobeniusModule.TraceCup.isAlt_pairing`: the pairing `H^d × H^d ⟶ K` is alternating for odd
  `d`.
-/

@[expose] public section

universe w v

namespace FrobeniusModule.TraceCup

variable {K : Type v} [Field K] {H : ℤ → FrobeniusModule.{max w v, v} K} {n : ℤ} {c : K}
  (T : TraceCup H n c)

/-- Blueprint `corollary-cup-product-pairing--3` (linear algebra): if `2 ≠ 0` in `K` (for
instance if `K` has characteristic zero) and `d` is odd, the trace–cup pairing
`H^d × H^d ⟶ K`, `d + d = n`, is alternating: `⟨x, x⟩ = 0`. By graded commutativity
(`FrobeniusModule.TraceCup.pairing_comm`), `⟨x, x⟩ = (-1)^{d·d} ⟨x, x⟩ = -⟨x, x⟩`. -/
theorem isAlt_pairing [NeZero (2 : K)] {d : ℤ} (hd : Odd d) (h : d + d = n) :
    (T.pairing d d h).IsAlt := by
  intro x
  have hc := T.pairing_comm d d h x x
  rw [(Int.negOnePow_eq_neg_one_iff _).2 (hd.mul hd), Units.smul_def, Units.val_neg,
    Units.val_one, neg_one_smul] at hc
  have h2 : (2 : K) * T.pairing d d h x x = 0 := by
    rw [two_mul]
    nth_rw 1 [hc]
    exact neg_add_cancel _
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

end FrobeniusModule.TraceCup
