/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology

/-!
# Support of a module on an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 04JY, 04K4 and 04KA
(blueprint: def-sfb-space-module-support).

A nonzero germ is represented by a section which cannot become zero on any further
etale neighbourhood of the point. Scheme points suffice: geometric points above a fixed
scheme point are conjugate, and a section defined on the scheme is invariant under this
conjugation. This describes the support without choosing geometric representatives.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of nonzero geometric germs, expressed by sections on etale charts.
The section `s` has nonzero germ at `x` precisely when no etale refinement with a point
above `x` kills it. If a geometric germ vanishes, its zero representative occurs on an
etale neighbourhood; conversely restriction of the zero section has zero germ. Sections
over the chart are invariant under conjugation of geometric lifts of `x`, so one may
quantify over ordinary chart points and all refinements as below.
Source: Stacks Project, Properties of Spaces, Tags 04JY, 04K4 and 04KA
(blueprint: def-sfb-space-module-support). -/
def moduleSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (M : X.Modules) :
    Set (Point X.obj.obj) :=
  {p | ∃ (T : X.EtaleSite) (x : (X.etaleForget.obj T)) (s : M.val.obj (op T)),
    schemePointMap T.obj.hom x = p ∧
      ∀ (U : X.EtaleSite) (f : U ⟶ T) (y : X.etaleForget.obj U),
        (X.etaleForget.map f).base y = x → M.val.map f.op s ≠ 0}

end AlgebraicGeometry.AlgebraicSpace
