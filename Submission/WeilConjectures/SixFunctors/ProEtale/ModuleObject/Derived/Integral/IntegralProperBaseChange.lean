/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Submission.WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperConstructibleCohomology
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import Submission.WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteStrataCompletion.FiniteStrataCompletionDetection
import all Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Proper base change with integral adic coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`
(blueprint: det-thm-sfb-proper-base-change-integral).

## Main statements

* `integralProperDirectImageAndFormulas`: proper direct image, derived Nakayama, and the
  proper base change and projection formula isomorphisms for integral coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.IsDerivedComplete

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
