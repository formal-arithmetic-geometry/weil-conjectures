/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback

import WeilConjectures.AlgebraicGeometry.ClosedCoverFrameTransitions
import WeilConjectures.AlgebraicGeometry.GlueComponentReducedCoverSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle

/-! # ExistsGluedInvertible

Source: Stacks Project, Varieties Lemma 09NE. -/

@[expose] public section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
-- Equality of transition coefficients suffices to glue the frame-preserving isomorphism.

end AlgebraicGeometry.Scheme.Modules
