/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Ample.AmpleOnReductionNoetherian
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Curve.ExistsAmpleOfReducedDimLEOne
import WeilConjectures.AlgebraicGeometry.Picard.PicardLift
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Ample invertible modules in dimension at most one

Source: Stacks Project, Varieties, Lemma 0A25 and Proposition 09NZ
(blueprint: lem-sc-dim-one-ample-invertible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
