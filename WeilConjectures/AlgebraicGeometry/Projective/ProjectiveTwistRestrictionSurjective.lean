/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution

/-!
# Eventual restriction onto a finite closed subscheme

Source: Stacks Project, Tag 0B5T (4), and the cohomology exact sequence.
(blueprint: lem-zl-projective-twist-restriction-surjective).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] tensorPullback

end

end AlgebraicGeometry
