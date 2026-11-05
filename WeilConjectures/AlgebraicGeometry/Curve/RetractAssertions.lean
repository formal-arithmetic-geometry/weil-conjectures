/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The eight curve assertions pass to retracts

Source: Stacks Project, Etale Cohomology, Section 03SB, proof of Lemma 03SD,
first paragraph (blueprint: lem-weil-pbc-curve-assertions-retract).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
