/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology

/-! # Absolute quasi-separatedness of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 0AHR
(blueprint: def-sfb-space-absolute-quasi-separated).

The affine-test criterion is equivalent to quasi-compactness of the absolute diagonal,
including when the specified base scheme is not quasi-separated.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Absolute quasi-separatedness, using the equivalent affine-test criterion.
Source: Stacks Project, Properties of Spaces, Tag 0AHR(3)
(blueprint: def-sfb-space-absolute-quasi-separated). -/
def IsAbsolutelyQuasiSeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ X.obj.obj),
    IsAffine U.left → IsAffine V.left → CompactSpace (Point (Limits.pullback a b))

end AlgebraicGeometry.AlgebraicSpace
