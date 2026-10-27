/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.SetTheory.Cardinal.Basic

/-! # The cardinal size of a scheme

Source: Stacks Project, sets.tex, section-categories-schemes, definition of size preceding
Tag 000I (blueprint: def-sfb-scheme-cardinal-size).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- The size of a scheme is the maximum of the countable cardinal, the cardinality of its
set of affine opens, and the supremum of the cardinalities of their rings of sections.
Here affine opens are actual open subsets, with their induced scheme structures, rather
than affine charts with a chosen presentation. The definition includes the empty scheme.

Source: Stacks Project, sets.tex, section-categories-schemes, definition preceding Tag 000I
(blueprint: def-sfb-scheme-cardinal-size). -/
noncomputable def cardinalSize (X : Scheme.{u}) : Cardinal.{u} :=
  max Cardinal.aleph0
    (max (Cardinal.mk X.affineOpens)
      (⨆ U : X.affineOpens, Cardinal.mk ↥Γ(X, U.1)))

end AlgebraicGeometry.Scheme
