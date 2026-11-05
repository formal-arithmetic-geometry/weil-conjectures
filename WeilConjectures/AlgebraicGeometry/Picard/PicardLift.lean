/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsEpi
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison
import WeilConjectures.Topology.Curve.NoetherianCohomologyDimOne
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-! # Lifting invertible modules along closed immersions in dimension at most one

Source: Stacks Project, Varieties, Lemma 09NY
(blueprint: lem-sc-pic-lift-closed-immersion-dim-le-one).
-/

@[expose] public section

universe u

open CategoryTheory
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
