/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Base change of a first order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.2.4 (Tag 09ZU), and
Schemes, Lemma 26.17.6 (Tag 01JU), part (1)
(blueprint: lem-weil-pbc-first-order-thickening-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a first order thickening is a first order thickening, with ideal
`i.ker.comap p`, the extended ideal of def-nagata-extended-ideal. The two projections
commute with `p` and `i`, giving a morphism of thickenings (Stacks Project, Tags 09ZU,
01JU (1), and 04EX (5)).

Proof:
1. By lem-weil-pbc-closed-immersion-base-change the first projection is a closed immersion.
2. On an affine open `V = Spec A` of the target, write the immersion as `Spec (A/K)`.
   The affine-cover criterion, open-preimage fibre product, and cartesian-square pasting
   identify the restricted base change with the fibre product over `Spec A`.
3. By lem-weil-pbc-quotient-base-change-closed-immersion-ideal its ideal on an affine
   `U = Spec B` above `V` is the extended ring ideal `KB`.
4. By lem-weil-pbc-module-pullback-ideal-quotient (1), the image of the tensor module
   pullback of the original ideal in the structure sheaf has the same sections `KB`.
   Such affine opens form a basis, so the two quasi-coherent ideal sheaves are equal.
   This extended ideal is represented by the recorded `IdealSheafData.comap`.
5. By part (2) of that lemma extension commutes with powers. The original ideal has
   square zero, so the extended ideal has square zero. Equivalently every product of
   two generators in `KB` vanishes because its two original factors multiply to zero.
6. The closed immersion and square-zero ideal give `IsFirstOrderThickening` by
   def-sbc-first-order-thickening. The pullback equation supplies the factorization
   through the original closed subscheme required for a morphism of thickenings.

(blueprint: lem-weil-pbc-first-order-thickening-base-change). -/
theorem IsFirstOrderThickening.baseChange {W W' Z' : Scheme.{u}}
    (i : W ⟶ W') (p : Z' ⟶ W') (hi : IsFirstOrderThickening i) :
    IsFirstOrderThickening (pullback.fst p i) ∧
      (pullback.fst p i).ker = i.ker.comap p ∧
      (i.ker.comap p) ^ 2 = ⊥ ∧
      pullback.fst p i ≫ p = pullback.snd p i ≫ i := by
  sorry

end AlgebraicGeometry
