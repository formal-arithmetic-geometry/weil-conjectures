/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective

/-!
# Relative dimension of a base change of a smooth curve

Source: Stacks Project, Tags 02NK, 02FY (1), 01VB and 0A21 (3)
(blueprint: lem-sc-curve-base-change-relative-dimension-one).

The base change and its second projection follow `def-pc-base-change`:
`pullback f g` and `pullback.snd f g`. "Smooth of relative dimension one" is the notion
recorded on `def-sbc-smooth-morphisms`, Mathlib's `SmoothOfRelativeDimension 1`.
The proof uses the existing relative-dimension comparison over a field and base-change
stability directly, without a separate fibre-dimension computation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth curve over a field remains smooth of relative dimension one after any base change.
Source: Stacks, Tags 02NK, 02FY (1), 01VB and 0A21 (3)
(blueprint: lem-sc-curve-base-change-relative-dimension-one).

Proof:
1. An integral curve is irreducible and has topological Krull dimension one by
   `IsIntegralCurve.topologicalKrullDim_eq_one`. Since `f` is smooth, the source-library
   theorem `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` gives
   `SmoothOfRelativeDimension 1 f`.
2. Smoothness of relative dimension one is stable under arbitrary base change. The
   source-library instance `smoothOfRelativeDimension_pullback_snd`, using Mathlib's
   `smoothOfRelativeDimension_isStableUnderBaseChange`, applies to `pullback.snd f g`.
   This also covers an empty base `T`.
-/
theorem curve_baseChange_smoothOfRelativeDimension_one {k : Type u} [Field k]
    {C T : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsIntegralCurve f] [Smooth f]
    (g : T ⟶ Spec (.of k)) :
    SmoothOfRelativeDimension 1 (pullback.snd f g) := by
  have : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mpr
      (by exact_mod_cast IsIntegralCurve.topologicalKrullDim_eq_one (f := f))
  infer_instance

end AlgebraicGeometry
