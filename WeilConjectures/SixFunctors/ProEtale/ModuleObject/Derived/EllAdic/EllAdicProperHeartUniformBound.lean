/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperConstructibleHeartBound
import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundRational
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Uniform proper heart amplitude over a Noetherian base

The finite-amplitude part of the proper heart theorem, independently of coproduct
continuity. Source: Bhatt--Scholze, Section 6.8, and blueprint proper heart bound.
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Sectionwise postcomposition, with the multiplication fixed as part of the ring object.

-- A small-universe specialization of the normed coefficient realization construction.

-- Minimality transports all closure operations at once along the exact equivalence.

-- A finite bound for the geometric fibres of a proper morphism to a Noetherian scheme.

-- Filtered colimits of constructibles keep a uniform bound, by qcqs continuity.

-- The filtered-colimit closure of finite-field constructibles contains the Serre closure.

-- The filtered-colimit closure of integral constructibles contains the Serre closure.

end AlgebraicGeometry.ProEtale.CondensedRing
