/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.Cr
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Tsen's theorem and the Brauer group of a curve

By Tsen's theorem the function field of a curve over an algebraically closed field is `C₁`, so
its Brauer group vanishes; and the Brauer group of a smooth curve vanishes as well, because it
injects into the Brauer group of its function field.

Curves are given by a structure morphism `f : C ⟶ Spec k` satisfying
`AlgebraicGeometry.IsCurve`.

## Main statements

- `AlgebraicGeometry.isCrField_functionField`: Tsen's theorem, the function field of an
  integral curve over an algebraically closed field is `C₁`.
- `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup_functionField`: the Brauer group of
  that function field vanishes.
- `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a smooth
  curve over an algebraically closed field vanishes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsCurve f]

-- The conclusions below do not mention `f`, so the structure morphism has to be included by hand.
include f

/-- **Tsen's theorem.** For an integral curve `C` over an algebraically closed field `k`, the
function field `k(C)` is a `C₁` field: every homogeneous form of degree `d` in `N > d`
variables over `k(C)` has a nontrivial zero.

The rational function field `k(t)` is `C₁` by a dimension count on tuples of polynomials of
bounded degree, and `k(C)` is a finite extension of `k(t)`, hence `C₁` by a norm-form argument.
Neither step uses smoothness or properness of `C`, so neither is assumed.
(blueprint: `sk-prop-tsen`) -/
theorem isCrField_functionField [IsIntegral C] : IsCrField C.functionField 1 :=
  sorry

/-- The Brauer group of the function field of an integral curve over an algebraically closed
field vanishes, `Br(k(C)) = H²(k(C), 𝔾ₘ) = 0`: by Tsen's theorem
`AlgebraicGeometry.isCrField_functionField` the field `k(C)` is `C₁`, and over a `C₁` field
the reduced norm of a central division algebra of degree `d > 1`, a form of degree `d` in
`d ^ 2 > d` variables, would have a nontrivial zero.
(blueprint: `sk-prop-tsen`) -/
theorem subsingleton_cohomologicalBrauerGroup_functionField [IsIntegral C] :
    Subsingleton (Spec C.functionField).CohomologicalBrauerGroup :=
  sorry

/-- **The Brauer group of a smooth curve vanishes.** For `C` a smooth curve over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`.

For `C` connected and proper, `Br(C)` injects into `Br(k(C))` by
`AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`, and the target vanishes by
`AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup_functionField`. Properness is not
assumed: the same injectivity holds for the regular integral affine curves, whose case is the
one the cohomological dimension of an affine curve needs.
(blueprint: `sk-thm-br`) -/
theorem subsingleton_cohomologicalBrauerGroup [Smooth f] :
    Subsingleton C.CohomologicalBrauerGroup :=
  sorry

end AlgebraicGeometry
