/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.Cr
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Tsen's theorem and the Brauer group of a curve

A `C₁` field has trivial Brauer group; by Tsen's theorem the function field of a curve over an
algebraically closed field is `C₁`, so its Brauer group vanishes; and the Brauer group of a
smooth curve vanishes as well, because it injects into the Brauer group of its function field.

Curves appear through the class `AlgebraicGeometry.IsCurveOver`; see the module docstring of
`WeilConjectures.AlgebraicGeometry.Curve.Defs`.

## Main statements

- `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup_of_isCr`: the Brauer group of a
  `C₁` field vanishes.
- `AlgebraicGeometry.isCr_functionField`: Tsen's theorem, the function field of a curve over
  an algebraically closed field is `C₁`.
- `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup_functionField`: hence the Brauer
  group of its function field vanishes.
- `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a smooth
  curve over an algebraically closed field vanishes.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **The Brauer group of a `C₁` field vanishes.** A finite central division algebra `D` over
`K` has dimension `d ^ 2`, and its reduced norm is a homogeneous form of degree `d` in `d ^ 2`
variables which vanishes only at `0`; if `d > 1` then `d ^ 2 > d`, so the `C₁` property
produces a nontrivial zero. Hence `d = 1`, and by Wedderburn every central simple algebra over
`K` is a matrix algebra. The proof is `sorry`.
(blueprint: `lem-sc-c1-brauer-trivial`) -/
theorem subsingleton_cohomologicalBrauerGroup_of_isCr (K : Type u) [Field K] [IsCr K 1] :
    Subsingleton (Spec (.of K)).CohomologicalBrauerGroup :=
  sorry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [IsCurveOver k C] [IsIntegral C]

-- The conclusions below do not mention `k`, so the base field has to be included by hand.
include k

/-- **Tsen's theorem.** For an integral curve `C` over an algebraically closed field `k`, the
function field `k(C)` is a `C₁` field: every homogeneous form of degree `d` in `N > d`
variables over `k(C)` has a nontrivial zero.

The proof has two steps: the rational function field `k(t)` is `C₁`, by a dimension count on
the space of tuples of polynomials of bounded degree; and `k(C)` is a finite extension of
`k(t)`, so it is `C₁` by `IsCr.of_finiteDimensional`. Neither step uses smoothness or
properness of `C`. The proof is `sorry`.
(blueprint: `lem-sc-tsen`) -/
theorem isCr_functionField : IsCr C.functionField 1 :=
  sorry

/-- The Brauer group of the function field of an integral curve over an algebraically closed
field vanishes: combine Tsen's theorem `AlgebraicGeometry.isCr_functionField` with
`AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup_of_isCr`.
(blueprint: `lem-sc-tsen`) -/
theorem subsingleton_cohomologicalBrauerGroup_functionField :
    Subsingleton (Spec C.functionField).CohomologicalBrauerGroup :=
  letI : IsCr C.functionField 1 := isCr_functionField (k := k) (C := C)
  subsingleton_cohomologicalBrauerGroup_of_isCr C.functionField

/-- **The Brauer group of a smooth curve vanishes.** For `C` a smooth integral curve over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`.

A smooth separated connected curve is either proper or affine. In the proper case `Br(C)`
injects into `Br(k(C))` by `AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`, and
the target vanishes by Tsen; the affine case is obtained from a compactification through the
divisor sequence. Properness is therefore *not* a hypothesis: the affine case is the one that
the cohomological dimension of an affine curve needs. The proof is `sorry`.
(blueprint: `lem-sc-brauer-zero`) -/
theorem subsingleton_cohomologicalBrauerGroup [Smooth (C ↘ Spec (.of k))] :
    Subsingleton C.CohomologicalBrauerGroup :=
  sorry

end AlgebraicGeometry
