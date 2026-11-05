/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The ordinary quotient-system tensor and its inverse-limit adjunction

Source: Stacks 03D7, 03EK, 0940 and 0941.

The strict quotient system of a completed-coefficient module is the system of its
scalar extensions to the finite quotients. It is left adjoint to restriction of
coefficients followed by inverse limit. This file records that ordinary adjunction
together with its normalizations, independently of any derived coefficient calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-! ### Generic scalar-extension transition comparisons

The following auxiliary statements are the generic transition comparison for the
sequence-site scalar models (Stacks 03D7, 03EK).
-/

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

section Generic
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory
namespace WeilConjectures.OrdinaryQuotient
open SemilinearSections

end WeilConjectures.OrdinaryQuotient
end Generic

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [instance] OrdinaryModel.additive

end WeilConjectures.OrdinaryQuotient

/-! ### The sequence-site construction of the ordinary quotient system -/

section Construction
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures.OrdinaryQuotient

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

end WeilConjectures.OrdinaryQuotient
end Construction

/-! ### The ordinary model -/

section Model
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section OrdinaryConstruction
attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf

end OrdinaryConstruction

section CanonicalComparisons

end CanonicalComparisons

end WeilConjectures.OrdinaryQuotient
end Model

-- Restore the incoming instance registration after using compact local sheaf instances.
attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
