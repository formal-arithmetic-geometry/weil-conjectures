/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsEpi
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-! # Brauer pullback to the reduction of a curve

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its cohomology claim.
(blueprint: lem-sc-brauer-reduction-injection)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

end AlgebraicGeometry.IsCurve
