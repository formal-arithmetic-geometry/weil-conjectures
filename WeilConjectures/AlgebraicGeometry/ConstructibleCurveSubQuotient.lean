/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveSubPart
import WeilConjectures.AlgebraicGeometry.ConstructibleCurveQuotPart
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionModulesAgree
import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Subobjects and quotients of constructible torsion sheaves on curves

Source: Stacks Project, Etale Cohomology, Proposition 09BH (2), with Definition 03RW
and Lemma 095E (blueprint: lem-weil-pbc-curve-constructible-sub-quotient).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.CurveCoefficientPair

end AlgebraicGeometry.CurveCoefficientPair
