/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.Variety
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange

/-!
# Relative dimension of a base change of a smooth curve

Source: Stacks Project, Tags 02NK, 02FY (1), 01VB and 0A21 (3)
(blueprint: lem-sc-curve-base-change-relative-dimension-one).

The base change and its second projection follow `def-pc-base-change`:
`pullback f g` and `pullback.snd f g`. "Smooth of relative dimension one" is the notion
recorded on `def-sbc-smooth-morphisms`, Mathlib's `SmoothOfRelativeDimension 1`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A smooth curve over a field remains smooth of relative dimension one after any base change.
Source: Stacks, Tags 02NK, 02FY (1), 01VB and 0A21 (3)
(blueprint: lem-sc-curve-base-change-relative-dimension-one).

Proof:
1. The projection `pullback.snd f g` is the base change of the smooth structure map `f`.
   Smoothness is stable under base change (`lem-pc-proper-base-change` (2), Tag 01VB,
   and `def-sbc-smooth-morphisms`).
2. For a point `x` of the pullback and its image `t` in `T`, pullback associativity
   identifies the fibre with `C ×_Spec k Spec κ(t)` (`def-pc-base-change` and
   `def-pc-scheme-fibre`), as expressed by `baseChange_fiber`.
3. By `lem-sc-fibre-dimension-after-base-change` (Tag 02FY (1)), the dimension of this
   fibre at `x` equals the dimension of `C` at the image of `x` in `C`: the fibre of
   `C → Spec k` over the unique point of `Spec k` is `C`. The curve definition
   (`def-pc-curve`) gives `C.dim = 1`; `lem-pc-scheme-dimension-local-rings` identifies
   this with topological dimension. Since `C` is integral, hence irreducible, and
   of finite type over `k`, `lem-sc-dimension-locally-algebraic` (Tag 0A21 (3)) gives
   local dimension one at every point of `C`. Thus every displayed fibre dimension is one.
4. Smoothness together with `dim_x((C_T)_t) = 1` at every point `x` (the point
   `asFiber x` of the scheme-theoretic fibre, dimension `topologicalKrullDimAt` of
   `def-kun-dimension`) is smoothness of relative dimension one in
   `def-sbc-smooth-morphisms`, i.e. `SmoothOfRelativeDimension 1` (Stacks 02G1, 02G2).
-/
theorem curve_baseChange_smoothOfRelativeDimension_one {k : Type u} [Field k]
    {C T : Scheme.{u}} (f : C ⟶ Spec (.of k)) [f.IsCurveOverField] [Smooth f]
    (g : T ⟶ Spec (.of k)) :
    SmoothOfRelativeDimension 1 (pullback.snd f g) := by
  sorry

end AlgebraicGeometry
