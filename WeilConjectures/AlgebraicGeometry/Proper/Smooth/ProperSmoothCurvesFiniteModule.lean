/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothConnectedFibreDimensionLoci
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesPrimeCoefficients
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ConnectedFibresConstantDegreeZero
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal
import WeilConjectures.ConstructibleSheaf.FiniteDerived
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructibility for proper smooth families of curves with finite coefficients

Source: Stacks Project, more-etale.tex, Tag 0GKW; Tag 0GK3 for dimension zero,
and morphisms.tex, Tag 02G1 for the fibre-dimension decomposition
(blueprint: lem-weil-pbc-etale-proper-smooth-curves-finite-module).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Compare the two models of the same higher direct image.

-- A nonempty smooth connected scheme over a field has a single relative dimension.

end AlgebraicGeometry.Etale
