/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Adic realizations of algebraic numbers

Source: Weil conjectures blueprint, `sec-zeta-weil`, unit `sk-thm-intfactors`,
`def-weil-algebraic-closure-q.md` (blueprint: def-weil-algebraic-closure-q).

The field of algebraic numbers inside the chosen coefficient field `C.Qbar` is the
existing intermediate field `algebraicClosure ℚ C.Qbar`. Its membership condition is
`IsAlgebraic ℚ z`, by `mem_algebraicClosure_iff`. Its field structure and inclusion of
`ℚ` are supplied by `IntermediateField`; they are not defined again here.

A realization is a rational algebra isomorphism from a fixed algebraic closure of `ℚ`
to that intermediate field. This definition does not choose a realization or assert
its existence; that is the downstream node `lem-weil-realization-exists`.
-/

@[expose] public section

universe u v

namespace WeilConjectures.FiniteFieldDatum.CoefficientDatum

/-- The rational algebra structure on the coefficient field is the composite of the
canonical embedding into the adic numbers with the chosen coefficient-field embedding.
It identifies `ℚ` with the prime subfield, without any additional choice.
Source: blueprint `sec-zeta-weil/sk-thm-intfactors/def-weil-algebraic-closure-q.md`
(blueprint: def-weil-algebraic-closure-q). -/
noncomputable instance ratAlgebra (D : WeilConjectures.FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) : Algebra ℚ C.Qbar :=
  ((algebraMap (Padic C.l) C.Qbar).comp (algebraMap ℚ (Padic C.l))).toAlgebra

/-- Realizations of algebraic numbers in the chosen algebraic closure of `ℚ_[C.l]`.
The datum `D` fixes `p`, `a ≥ 1`, `q = p ^ a`, `k₀` and its algebraic closure; `C`
fixes the prime `C.l ≠ D.p` and its coefficient field. The field `Qbar` is any fixed
algebraic closure of `ℚ`. The target is precisely the subfield of elements algebraic
over `ℚ`, and `AlgEquiv` means a bijective `ℚ`-embedding.
Source: blueprint `sec-zeta-weil/sk-thm-intfactors/def-weil-algebraic-closure-q.md`
(blueprint: def-weil-algebraic-closure-q). -/
def AlgebraicNumberRealization (D : WeilConjectures.FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) (Qbar : Type v) [Field Qbar] [Algebra ℚ Qbar]
    [IsAlgClosure ℚ Qbar] : Type (max u v) :=
  Qbar ≃ₐ[ℚ] algebraicClosure ℚ C.Qbar

end WeilConjectures.FiniteFieldDatum.CoefficientDatum
