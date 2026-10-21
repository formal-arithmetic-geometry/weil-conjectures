/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.StrictCoefficientExchangeArrows
import Sheaf.Paper.RingedSquareTensorCompatibility

/-! # Normalization of strict coefficient reduction

Source: Stacks Project, sites-cohomology.tex, Tags 0944, 0E48 and 0A07.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

variable {S T X Y : RingedTensorCorner.{u, w}}
  (f : RingedTensorEdge S X) (g : RingedTensorEdge S T)
  (h : RingedTensorEdge X Y) (e : RingedTensorEdge T Y)
  [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} S.projectionTowers]
  [HasDerivedCategory.{w} T.projectionTowers]
  [HasDerivedCategory.{w} X.projectionTowers]
  [HasDerivedCategory.{w} Y.projectionTowers]

variable [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
  {lS : StrictProjectionLimit S} {lT : StrictProjectionLimit T}
  {lX : StrictProjectionLimit X} {lY : StrictProjectionLimit Y}
  {dg : StrictProjectionDirectImage g lT lS} {dh : StrictProjectionDirectImage h lY lX}

variable {f g h e}

/-- The normalized derived coefficient pullbacks respect the ringed square.
Source: Stacks Project, Tag 0E48, the two pullback/tensor paths in the diagram;
strict diagram refinement (blueprint: lem-sbc-strict-reduction-pullback-square).

Proof: Restrict the two natural transformations to flat K-flat representatives on S.
Use each PullReduction.normalized equation to replace its pullback comparison by
chainTensorPullback followed by the coefficient comparison. Derived pullback is
computed by the exact termwise functor. At each degree and tower index the two
maps agree by the coefficient square equation and associativity of the canonical
ringed tensor pullback comparison: both send a pure tensor to the same tensor of
its inverse images. The totalization maps have degree zero and introduce no signs.
Equality at each degree and index proves equality of the strict complex maps.
Cancel the representative comparison isomorphisms. K-flat resolutions present the
derived category, so injectivity of restriction proves the natural-transformation
equality on all inputs. This uses equality of strict complex maps before localization,
never equality detected by derived evaluations. -/
theorem strictReductionPullbackSquare
    (s : RingedTensorSquare S T X Y g f e h) (q : Coefficients f g h e s)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap) (M : S.mateDerived) :
    (towerLeft h).map (q.pf.pull.hom.app M) ≫
        q.ph.pull.hom.app (f.left.obj M) ≫
        q.atY.r.functor.map (s.derivedComparison.hom.app M) =
      (towerSquare f g h e s).hom.app (q.atS.r.functor.obj M) ≫
        (towerLeft e).map (q.pg.pull.hom.app M) ≫
        q.pe.pull.hom.app (g.left.obj M) := by
  sorry

end SheafOfModules.StrictQuotientExchange
