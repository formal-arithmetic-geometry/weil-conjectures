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
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PrimeCurveGeometricStalkFinite
import WeilConjectures.AlgebraicGeometry.Module.ModuleSpecializationAbelianIso
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteStalkSpecializationCriterion
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothProperPrimeSpecialization
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-!
# Prime coefficients in proper smooth curve families

Source: Stacks Project, more-etale.tex, Tag 0GKV, lemma-proper-smooth-family-curves,
the Noetherian case (blueprint: lem-weil-pbc-proper-smooth-curves-prime-coefficients).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
