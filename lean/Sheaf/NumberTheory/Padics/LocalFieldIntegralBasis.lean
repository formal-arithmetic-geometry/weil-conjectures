/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-!
# Integral bases for finite extensions of local coefficient fields

Source: Weil conjectures blueprint, finite-free coefficient detail
(blueprint: lem-sfb-local-field-integral-basis).
-/

@[expose] public section

universe u v

namespace Padic

/--
For a finite tower of coefficient fields, the unit ball of the upper field has an
integral basis over the unit ball of the lower field.

Source: Weil conjectures blueprint, `sk-prop-sfb-cartesian-coefficients-finite-free.proof.md`,
opening sentence (blueprint: lem-sfb-local-field-integral-basis).

Proof:
1. Write the unit balls as `A` and `B`. By
   `lem-weil-l-adic-extension-integers-dvr` and `def-sc-discrete-valuation-ring`,
   `A` is a DVR and a principal ideal domain, hence Noetherian by
   `lem-weil-pbc-pid-noetherian-normal`. Compatibility makes `B` an `A`-module.
   The field `E` is complete by `lem-weil-l-adic-extension-complete`, and its
   absolute value is nontrivial because the value of `l` is `l⁻¹ < 1`.
2. Choose an `E`-basis of `F` with coordinates `c_i`. The coordinate linear
   equivalence is a homeomorphism by
   `lem-weil-pbc-finite-dimensional-linear-homeomorphism`: the absolute-value
   topologies are Hausdorff, and compatibility makes the inclusion isometric,
   so scalar multiplication is continuous. Thus some `ε > 0` satisfies
   `|y| < ε → |c_i(y)| < 1` for every `i`.
3. Choose `N ≥ 0` with `l⁻ᴺ < ε`. For `x ∈ B`, the coordinates of `lᴺ x`
   belong to `A`. Therefore `B` lies in the single finitely generated lattice
   spanned over `A` by `l⁻ᴺ` times the chosen field basis.
4. By `lem-weil-pbc-noetherian-submodule-finite`, `B` is finitely generated over
   `A`. It is torsion-free because it embeds in the field `F`. Apply
   `lem-sc-dvr-fg-torsionfree-free` to obtain a finite `A`-basis of `B`.
5. This basis spans `F` over `E`: multiply any field element by a sufficiently
   large power of `l` to put it in `B`, expand there, and divide back. It is
   also `E`-linearly independent: multiply any finite relation by one power
   of `l` that puts all coefficients in `A`, then use `A`-linear independence
   and cancel that nonzero power.
6. By `def-weil-vector-space-dimension`, this field basis has cardinality
   `Module.finrank E F`. Reindex the integral basis accordingly. Its elements
   lie in `B`, and its basis coordinates give exactly the asserted integral
   expansion and uniqueness.
-/
theorem exists_integral_basis
    (l : ℕ) [Fact l.Prime]
    (E : Type u) (F : Type v)
    [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [Algebra E F] [IsScalarTower (Padic l) E F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    [FiniteDimensional E F]
    (hcompat : ∀ x : E,
      coefficientExtensionAbsoluteValue l F (algebraMap E F x) =
        coefficientExtensionAbsoluteValue l E x) :
    ∃ b : Fin (Module.finrank E F) → F,
      (∀ i, b i ∈ coefficientExtensionIntegers l F) ∧
        ∀ x : F, x ∈ coefficientExtensionIntegers l F →
          ∃! a : Fin (Module.finrank E F) → E,
            (∀ i, a i ∈ coefficientExtensionIntegers l E) ∧
              x = ∑ i, algebraMap E F (a i) * b i := by
  sorry

end Padic
