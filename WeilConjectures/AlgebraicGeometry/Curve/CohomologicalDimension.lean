/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The étale cohomological dimension of a curve

The étale cohomological dimension of a smooth connected curve over an algebraically closed
field is at most two, and at most one if the curve is affine. Both statements are recorded for
sheaves killed by a nonzero integer `n`; a general torsion sheaf is the filtered colimit of
such subsheaves and cohomology on a quasi-compact quasi-separated scheme commutes with
filtered colimits, so nothing is lost — this is why `AlgebraicGeometry.IsCurveOver` asks for
finite type rather than only locally of finite type.

Curves appear through the class `AlgebraicGeometry.IsConnectedCurveOver`; see the module
docstring of `WeilConjectures.AlgebraicGeometry.Curve.Defs`.

## Main statements

- `AlgebraicGeometry.subsingleton_sheafH_of_three_le`: `H^q(C, F) = 0` for `q ≥ 3`.
- `AlgebraicGeometry.subsingleton_sheafH_of_two_le_of_isAffine`: `H^q(C, F) = 0` for `q ≥ 2`
  on an affine curve.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
  [IsConnectedCurveOver k C] [Smooth (C ↘ Spec (.of k))]

-- The conclusions below do not mention `k`, so the base field has to be included by hand.
include k

/-- **Vanishing in high degrees.** Let `C` be a smooth connected curve over an algebraically
closed field `k`. Then `H^q(C, F) = 0` for `q ≥ 3` and every étale sheaf `F` killed by a
nonzero integer `n`: the étale cohomological dimension of a smooth curve over an algebraically
closed field is at most two.

There is no hypothesis relating `n` to `char k`: the `p`-primary part in characteristic `p` is
handled by the Artin–Schreier sequence. The sharper bound `≤ 1` for `C` affine is
`AlgebraicGeometry.subsingleton_sheafH_of_two_le_of_isAffine`. The proof is `sorry`.
(blueprint: `lem-sc-cohomological-dimension`) -/
theorem subsingleton_sheafH_of_three_le (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0)
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H F q) :=
  sorry

/-- **Cohomological dimension of an affine curve.** Let `k` be algebraically closed and let `C`
be a smooth connected *affine* curve over `k`. Then `H^q(C, F) = 0` for `q ≥ 2` and every
étale sheaf `F` killed by a nonzero integer `n`: the étale cohomological dimension of a smooth
affine curve over an algebraically closed field is at most one.

Degrees `q ≥ 3` are `AlgebraicGeometry.subsingleton_sheafH_of_three_le`; degree two uses the
vanishing of the Brauer group of an affine curve. The proof is `sorry`.
(blueprint: `lem-sc-affine-cohomological-dimension`) -/
theorem subsingleton_sheafH_of_two_le_of_isAffine [IsAffine C] (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0)
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H F q) :=
  sorry

end AlgebraicGeometry
