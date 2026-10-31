/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses

/-!
# Smooth-proper data over a finite field

Source: Weil conjectures blueprint, `sec-zeta-weil`,
`sk-the-five-assembled-theorems--remark-1`, Definition [Smooth-proper datum],
label `def:smooth-proper-datum`, lines 2868--2876
(blueprint: def-weil-smooth-proper-datum).

The datum packages a finite-field datum, a finite-type scheme over its base field,
its nonnegative pure dimension, and the smoothness, properness, and geometric
connectedness hypotheses.  The geometric fibre is a canonical projection of the
record, so it is exposed as a definition rather than as independently chosen data.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- A smooth, proper, geometrically connected finite-type scheme over the base
field in a global finite-field datum, together with its pure dimension.

The geometric fibre is the canonical base change supplied by
`FiniteFieldDatum.geometricFiber`; it is therefore a function of this record.
Source: Weil conjectures blueprint, `sec-zeta-weil`,
`sk-the-five-assembled-theorems--remark-1`, Definition [Smooth-proper datum],
label `def:smooth-proper-datum` (blueprint: def-weil-smooth-proper-datum).
-/
structure SmoothProperDatum (D : FiniteFieldDatum.{u}) where
  X₀ : Over (Spec (CommRingCat.of D.k₀))
  [isProper : IsProper X₀.hom]
  d : ℕ
  smoothOfPureDimension : D.IsSmoothOfPureDimension X₀ d
  [geometricallyConnected : GeometricallyConnected X₀.hom]

/-- The geometric fibre in a smooth-proper datum.
Source: Weil conjectures blueprint, `sec-zeta-weil`,
`sk-the-five-assembled-theorems--remark-1`, Definition [Smooth-proper datum],
label `def:smooth-proper-datum` (blueprint: def-weil-smooth-proper-datum).
-/
noncomputable def SmoothProperDatum.X {D : FiniteFieldDatum.{u}}
    (𝓧 : SmoothProperDatum D) :
    Over (Spec (CommRingCat.of D.k)) :=
  letI : IsProper 𝓧.X₀.hom := 𝓧.isProper
  D.geometricFiber 𝓧.X₀

end WeilConjectures
