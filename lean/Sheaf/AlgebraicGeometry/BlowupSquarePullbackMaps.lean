module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback

/-!
# Maps associated to a flat blowup square

Source: Stacks Project, `divisors.tex`, Tags 0805 and 080D; `flat.tex`, Tag 0814,
proof paragraphs 1--2 (blueprint: def-trf-blowup-square-pullback-maps).

This module re-exports `moduleStrictTransformFlatPullbackMap` and
`moduleStrictTransformFlatPullbackSourceIso`, retaining their original names and data.
They are the induced map of blown-up sources and the section-normalized comparison
of ordinary module pullbacks. Neither construction uses the strict-transform comparison
theorem. The abbreviation below is a transparent entry point to the first construction;
it does not choose or reconstruct a map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The induced morphism of blown-up sources, re-exported without a second construction.
Its projections are the original source map after the first projection, and the flat
blowup base-change map after the second projection. The same public import re-exports
`moduleStrictTransformFlatPullbackSourceIso`, whose data are the section-normalized
composition comparisons and this morphism's first-projection equality.
Source: Stacks Tags 0805 and 080D, and Tag 0814, proof paragraphs 1--2
(blueprint: def-trf-blowup-square-pullback-maps). -/
noncomputable abbrev blowupSquarePullbackMap {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] (I : S.IdealSheafData) :
    Limits.pullback g (I.comap e).blowupMap ⟶ Limits.pullback f I.blowupMap :=
  moduleStrictTransformFlatPullbackMap f e g j h I

end AlgebraicGeometry.Scheme.Modules
