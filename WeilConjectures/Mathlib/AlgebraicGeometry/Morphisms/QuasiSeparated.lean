/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-compactness of the inclusion of a quasi-compact open

`AlgebraicGeometry.Scheme.Opens.quasiCompact_ι`: the inclusion of a quasi-compact open of
a quasi-separated scheme is a quasi-compact morphism.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The inclusion of a quasi-compact open of a quasi-separated scheme is a quasi-compact
morphism. -/
lemma Scheme.Opens.quasiCompact_ι {X : Scheme.{u}} [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : QuasiCompact U.ι :=
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  inferInstance

end AlgebraicGeometry
