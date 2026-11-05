/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import Mathlib.Topology.JacobsonSpace

/-!

# Charts for Deligne's induction for the change of trait

Geometric inputs of the proof of `NearbyCyclesModel.traitChangeInvariance`:

* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.exists_isAffineOpen`: the charts of a
  morphism locally embedding into affine spaces may be taken on affine opens;
* `AlgebraicGeometry.AffineSpace.isImmersion_lift_isPullback_map`: a chart restricts to a chart of
  a cartesian fibre;
* `AlgebraicGeometry.not_isClosed_singleton_of_isOpenImmersion`: a point of an open of a Jacobson
  scheme which is not closed in the scheme is not closed in the open.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
