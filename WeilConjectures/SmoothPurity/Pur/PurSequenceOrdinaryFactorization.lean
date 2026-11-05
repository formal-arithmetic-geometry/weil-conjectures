/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import all WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTransitionComparison
import WeilConjectures.SmoothPurity.Pur.PurSequenceConstantRingFactorization
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The ordinary quotient projection and its constant-ring factorization

Source: Stacks Project, Tags 03D7 and 0940
(blueprint: lem-pur-sequence-ordinary-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
namespace WeilConjectures

open SemilinearSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted normalizedDVRQuotient
  completedIntegralCommRingProjectionUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence scalarReductionExtension
  coefficientFiniteDerivedExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory

open SemilinearSections

attribute [local irreducible] coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
  coefficientQuotientNatTrans

end WeilConjectures

-- Restore the incoming instance registration after using compact local sheaf instances.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
