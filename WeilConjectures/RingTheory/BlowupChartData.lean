/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TangentCone
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A chart of the blow-up of a regular local surface separating two curves

Let `R` be a henselian regular local ring of dimension `2` with algebraically closed residue field
`κ`, and let `D = V(f)`, `B = V(g)` be curves and `H = V(h)` a regular curve through the closed
point `t` such that the tangent cones satisfy `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`.
Blowing up `t` separates `D` from `B` and from `H` (blueprint `det-tf-blowup-configuration`,
`det-tf-blowup-strict-transform`). After a generic choice of the regular system of parameters
`(x, y)`, all the points of the exceptional divisor that matter lie on the single affine chart
`R[T]/(xT - y)` of the blow-up (`blowupChart x y`). This file records what is used of this chart,
`AlgebraicGeometry.BlowupChartData`; with `f = x^d f'`, `h = x h'` on the chart,
`Z = Spec (R[T]/(xT - y))[1/f']` is the open part of the chart off the strict transform `D'`,
`Y = V(x) ⊆ Z` is the exceptional divisor and `X = V(h') ⊆ Z` the strict transform of `H`:

* `Z - Y = Spec R[1/(xf)]` and `Z - (X ∪ Y) = Spec R[1/(xfh)]`;
* `Y` and `X` are regular divisors, `Y` is connected and `X ∩ Y` is a reduced point;
* the strict transform of `B` is `Spec A'` for a finite `R/(g)`-algebra `A'`, all of whose closed
  points lie on `Y`, with `A'[1/x] = (R/g)[1/x]`;
* `B ∩ V(x) = {t}`.

## Main definitions

- `AlgebraicGeometry.BlowupChartData f g h x₀ y₀ c`: the chart data, for the parameters
  `x = x₀ + c i y₀`
  and `y = y₀`, `i` an index of the family of constants `c`.

## Main results

- `AlgebraicGeometry.nonempty_blowupChartData`: the chart data exist.
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial

namespace AlgebraicGeometry

section Data

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The data of a chart `R[T]/(xT - y)` of the blow-up of `Spec R` at its closed point which
separates the strict transforms of the curves `D = V(f)` and `B = V(g)` and meets the strict
transform of the regular curve `H = V(h)` transversally away from `D` (blueprint
`det-tf-blowup-configuration` and `det-tf-blowup-strict-transform`, in the chart containing all
the relevant points of the exceptional divisor). The regular system of parameters is
`x = x₀ + c i y₀`, `y = y₀` for an index `i` of the family of constants `c`. -/
structure BlowupChartData (f g h x₀ y₀ : R) {K : Type v} (c : K → R) where
  /-- the index of the constant in `x = x₀ + c i y₀` -/
  i : K
  /-- the order of `f` -/
  d : ℕ
  /-- the strict transform equation of `D` on the chart: `f = x^d f'` -/
  f' : blowupChart (x₀ + c i * y₀) y₀
  /-- the strict transform equation of `H` on the chart: `h = x h'` -/
  h' : blowupChart (x₀ + c i * y₀) y₀
  algebraMap_f : algebraMap R (blowupChart (x₀ + c i * y₀) y₀) f =
    algebraMap R _ (x₀ + c i * y₀) ^ d * f'
  algebraMap_h : algebraMap R (blowupChart (x₀ + c i * y₀) y₀) h =
    algebraMap R _ (x₀ + c i * y₀) * h'
  /-- `Z - Y = Spec R[1/(xf)]`: inverting `x` on `Z = Spec (R[T]/(xT - y))[1/f']` is inverting
  `xf` on `R`. -/
  isLocalization_x : IsLocalization.Away ((x₀ + c i * y₀) * f)
    (Localization.Away (algebraMap R (Localization.Away f') (x₀ + c i * y₀)))
  /-- `Z - (X ∪ Y) = Spec R[1/(xfh)]`. -/
  isLocalization_xh : IsLocalization.Away ((x₀ + c i * y₀) * f * h)
    (Localization.Away (algebraMap R (Localization.Away f') (x₀ + c i * y₀) *
      algebraMap _ (Localization.Away f') h'))
  /-- `x` is a non-zero-divisor on `Z`, so `Y = V(x)` is an effective Cartier divisor. -/
  x_mem_nonZeroDivisors : algebraMap R (Localization.Away f') (x₀ + c i * y₀) ∈
    nonZeroDivisors (Localization.Away f')
  /-- `h'` is a non-zero-divisor on `Z`, so `X = V(h')` is an effective Cartier divisor. -/
  h'_mem_nonZeroDivisors : algebraMap _ (Localization.Away f') h' ∈
    nonZeroDivisors (Localization.Away f')
  /-- `Y = V(x)` is integral (in particular connected). -/
  isDomain_quotient_x : IsDomain (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀)})
  /-- `Y = V(x)` is regular. -/
  isRegularRing_quotient_x : IsRegularRing (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀)})
  /-- `X = V(h')` is regular. -/
  isRegularRing_quotient_h' : IsRegularRing (Localization.Away f' ⧸
    Ideal.span {algebraMap _ (Localization.Away f') h'})
  /-- `X ∩ Y` is a reduced point. -/
  isField_quotient : IsField (Localization.Away f' ⧸
    Ideal.span {algebraMap R (Localization.Away f') (x₀ + c i * y₀),
      algebraMap _ (Localization.Away f') h'})
  /-- `B ∩ V(x) = {t}`. -/
  maximalIdeal_le_radical : maximalIdeal R ≤ (Ideal.span {x₀ + c i * y₀, g}).radical
  /-- the coordinate ring of the strict transform `B'` of `B` on the chart -/
  A' : Type u
  [commRing : CommRing A']
  [algebra : Algebra (R ⧸ Ideal.span {g}) A']
  [finite : Module.Finite (R ⧸ Ideal.span {g}) A']
  /-- `B' ⊆ Z`: the strict transform of `B` misses `D'`. -/
  toA' : Localization.Away f' →+* A'
  toA'_algebraMap (r : R) : toA' (algebraMap R _ r) =
    algebraMap (R ⧸ Ideal.span {g}) A' (Ideal.Quotient.mk _ r)
  /-- `B' - V(x) = B - t`. -/
  isLocalization_A' : IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {g}) (x₀ + c i * y₀))
    (Localization.Away (algebraMap (R ⧸ Ideal.span {g}) A'
      (Ideal.Quotient.mk _ (x₀ + c i * y₀))))
  /-- the closed points of `B'` lie on `Y = V(x)` -/
  mem_jacobson : algebraMap (R ⧸ Ideal.span {g}) A' (Ideal.Quotient.mk _ (x₀ + c i * y₀)) ∈
    Ideal.jacobson (⊥ : Ideal A')

attribute [instance] BlowupChartData.commRing BlowupChartData.algebra BlowupChartData.finite

end Data

variable {R : Type u} [CommRing R]

/-- **The separating chart of the blow-up exists** (blueprint `det-tf-blowup-configuration` and
`det-tf-blowup-strict-transform`, in a chart). Let `R` be a henselian regular local ring of
dimension `2` with algebraically closed residue field, `(x₀, y₀)` a regular system of parameters,
and `c` an infinite family of elements of `R` with distinct residues. Let `f, g` and `h` be such
that `h ∈ 𝔪 ∖ 𝔪²` and the tangent cones satisfy `C_t V(f) ∩ C_t V(g) = {0}` and
`C_t V(f) ∩ T_t V(h) = {0}`. Then for some index `i`, the chart `R[T]/(xT - y)` of the blow-up
for `x = x₀ + c i y₀`, `y = y₀` carries the data `BlowupChartData`. -/
theorem nonempty_blowupChartData [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {x₀ y₀ : R} (hm : maximalIdeal R = Ideal.span {x₀, y₀}) {K : Type v} [Infinite K]
    (c : K → R) (hc : Function.Injective (residue R ∘ c)) {f g h : R}
    (hDB : TangentConesMeetAtOrigin f g) (hDH : TangentConesMeetAtOrigin f h)
    (hh : HasOrder h 1) :
    Nonempty (BlowupChartData f g h x₀ y₀ c) :=
  sorry

end AlgebraicGeometry
