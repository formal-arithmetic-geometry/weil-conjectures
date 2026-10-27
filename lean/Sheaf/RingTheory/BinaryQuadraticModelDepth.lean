/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.DepthOverQuotientRing

/-! # Depth of a binary quadratic formal hypersurface

Source: Stacks Project, Curves, Tags 0C4C (`lemma-fitting-ideal`, (1) implies (3))
and 0C49 (`lemma-nodal-algebraic`), with the regular-sequence depth computation
from Algebra, Tags 00NQ, 090R and 0AUK
(blueprint: lem-trf-binary-quadratic-model-depth).
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace MvPowerSeries

/-- A two-variable formal power series ring over a field has depth two; its quotient
by any nonzero binary quadratic form is local, has maximal ideal the image of `(u,v)`,
and has intrinsic ring depth one, in every characteristic.
Source: Stacks Project, Curves, Tags 0C4C and 0C49; Algebra, Tags 00NQ, 090R and 0AUK
(blueprint: lem-trf-binary-quadratic-model-depth).

Proof:
1. Apply `lem-weil-pbc-power-series-field-cohen-regular-complete` with coefficient
   field `F` and two variables. The ambient ring is a Noetherian local domain, regular
   of dimension two, with maximal ideal `(u,v)`. Apply
   `lem-trf-regular-local-regular-sequence-depth` to its empty regular sequence to get
   ambient depth two (Algebra, Tag 00NQ).
2. The coefficients of `Q` at the three distinct exponent pairs `(2,0)`, `(1,1)`,
   and `(0,2)` are `a`, `b`, and `c`, by `def-weil-pbc-multivariate-power-series`.
   Since they are not all zero, `Q` is nonzero. The identity
   `Q = u * (a*u + b*v) + v * (c*v)` puts it in the maximal ideal. The ambient domain
   property makes multiplication by `Q` injective.
3. Apply `lem-weil-pbc-depth-drops-by-one` to the finite, nonzero self-module of the
   ambient ring and the nonzerodivisor `Q`. Its quotient is nonzero and has depth one
   as a module over the ambient ring (Algebra, Tag 090R).
4. The principal ideal `(Q)` is contained in `(u,v)` and annihilates the quotient.
   Apply `lem-weil-pbc-depth-over-quotient-ring` with this ideal and the quotient module.
   This supplies the local quotient, identifies its maximal ideal as the image of
   `(u,v)`, and identifies its intrinsic ring depth with the ambient-module depth
   computed in step 3 (Algebra, Tag 0AUK). None of these steps uses the characteristic
   or discriminant; the nonzero-discriminant case follows in particular. -/
theorem binary_quadratic_model_depth
    (F : Type u) [Field F] (a b c : F) (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (Q : MvPowerSeries (Fin 2) F)
    (hQ : Q = C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2) :
    IsLocalRing.depth (R := MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) F) = 2 ∧
      ∃ (_ : IsLocalRing (MvPowerSeries (Fin 2) F ⧸ Ideal.span {Q})),
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) F ⧸ Ideal.span {Q}) =
          Ideal.map (Ideal.Quotient.mk (Ideal.span {Q}))
            (Ideal.span ({X 0, X 1} : Set (MvPowerSeries (Fin 2) F))) ∧
        IsLocalRing.depth (R := MvPowerSeries (Fin 2) F ⧸ Ideal.span {Q})
          (MvPowerSeries (Fin 2) F ⧸ Ideal.span {Q}) = 1 := by
  sorry

end MvPowerSeries
