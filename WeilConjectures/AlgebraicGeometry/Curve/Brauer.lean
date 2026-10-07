/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup
public import WeilConjectures.FieldTheory.Tsen
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Tsen's theorem and the Brauer group of a curve

The function field of an integral curve over an algebraically closed field is `C₁`, so its
Brauer group vanishes; and the Brauer group of every curve over an algebraically closed field
vanishes.

Curves are given by a structure morphism `f : C ⟶ Spec k` satisfying
`AlgebraicGeometry.IsCurve`.

## Main statements

- `AlgebraicGeometry.IsCurve.isQuasiAlgClosed_functionField`: Tsen's theorem, the function
  field of an integral curve over an algebraically closed field is `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_functionField`: the Brauer
  group of that function field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a
  curve over an algebraically closed field vanishes.

## Implementation notes

The field-theoretic statements, Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one` and the
vanishing `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`, are the reusable ones; the
function-field statements here are their specialisations to curves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Tsen's theorem for curves.** For an integral curve `C` over an algebraically closed
field `k`, the function field `k(C)` is quasi-algebraically closed: every homogeneous form of
degree `d` in `N > d` variables over `k(C)` has a nontrivial zero. Neither smoothness nor
properness of `C` is assumed.
(blueprint: `sk-prop-tsen`) -/
theorem isQuasiAlgClosed_functionField (f : C ⟶ Spec (.of k)) [IsCurve f] [IsIntegral C] :
    IsQuasiAlgClosed C.functionField :=
  -- Proof sketch: `k(C)` has transcendence degree at most one over `k`, since `C` has
  -- dimension at most one, so this is `IsQuasiAlgClosed.of_trdeg_le_one`.
  sorry

/-- The Brauer group of the function field of an integral curve over an algebraically closed
field vanishes, `Br(k(C)) = H²(k(C), 𝔾ₘ) = 0`.
(blueprint: `sk-prop-tsen`) -/
theorem subsingleton_cohomologicalBrauerGroup_functionField (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsIntegral C] : Subsingleton (Spec C.functionField).CohomologicalBrauerGroup :=
  have := isQuasiAlgClosed_functionField f
  IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup C.functionField

/-- **The Brauer group of a curve vanishes.** For a curve `C` over an algebraically closed
field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Neither smoothness nor properness is assumed.
(blueprint: `sk-thm-br`) -/
theorem subsingleton_cohomologicalBrauerGroup (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton C.CohomologicalBrauerGroup :=
  -- Proof sketch.
  -- * Smooth case: `H²(C, 𝔾ₘ)` is the product over the connected components of `C`, each of
  --   which is integral, noetherian and regular. On such a component `Br` injects into
  --   `Br(k(C))` by `AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`, and the
  --   target vanishes by `subsingleton_cohomologicalBrauerGroup_functionField`.
  -- * Reduced case: for the normalisation `ν : C̃ ⟶ C` the cokernel `Q` of `𝔾ₘ ⟶ ν_* 𝔾ₘ` is
  --   supported on the finitely many singular points, so `H¹(C, Q) = 0`, and
  --   `H²(C, ν_* 𝔾ₘ) = H²(C̃, 𝔾ₘ) = 0` since `ν` is finite and `C̃` is smooth.
  -- * General case: with `𝒩` the nilradical, `1 + 𝒩` has a finite filtration whose graded
  --   pieces are coherent, and these have no `H²` on a scheme of dimension at most one.
  sorry

end AlgebraicGeometry.IsCurve
