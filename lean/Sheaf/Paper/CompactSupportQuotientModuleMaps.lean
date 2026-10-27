/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientCocycleData
public import Sheaf.Paper.CompactSupportOrdinaryQuotient

/-! # Chain-level quotient and balancing maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-module-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionExtension

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized ordinary integral reduction adjunction, in the sheaf-ring API.
Source: Stacks Tag 03CZ; the existing normalized unit determines this adjunction
(blueprint: lem-coef-compact-support-quotient-module-maps). -/
def compactSupportOrdinaryAdjunction (W : Scheme.{u}) (n : ℕ) :
    scalarReductionExtension.{u, u} l E W n ⊣
      pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E W n) :=
  (scalarReductionExtension_adjunction.{u, u} l E W n).choose

/-- The ordinary quotient transformation, constructed by transposing the final unit.
Source: Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-module-maps). -/
def compactSupportQuotientModuleMap (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    scalarReductionExtension.{u, u} l E W m ⟶
      scalarReductionExtension.{u, u} l E W n ⋙
        proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h) :=
  quotientTransitionNat (compactSupportOrdinaryAdjunction l E W m)
    (compactSupportOrdinaryAdjunction l E W n)
    (pbcRestrict (compactSupportLevelSheafQuotient l E W m n h))
    (pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted l E W m)
      (compactSupportLevelSheafQuotient l E W m n h)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W m n h))

/-- The balancing isomorphism is the canonical comparison of composed left adjoints.
Source: ordinary tensor associativity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-module-maps). -/
def compactSupportQuotientBalance (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    scalarReductionExtension.{u, u} l E W m ⋙
        pbcExtend (compactSupportLevelSheafQuotient l E W m n h) ≅
      scalarReductionExtension.{u, u} l E W n :=
  Adjunction.leftAdjointCompIso (compactSupportOrdinaryAdjunction l E W m)
    (pbcScalarAdjunction (compactSupportLevelSheafQuotient l E W m n h))
    (compactSupportOrdinaryAdjunction l E W n)
    (pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted l E W m)
      (compactSupportLevelSheafQuotient l E W m n h)
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      (compactSupportProjection_comp l E W m n h))

/-- The quotient transformation has its pure-tensor formula.
Source: ordinary adjunction unit and tensor scalar linearity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-module-maps). -/
theorem compactSupportQuotientModuleMap_formula (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource.{u, u} l E W) (U : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
      (x : M.val.obj U) :
      HEq (((compactSupportQuotientModuleMap l E W m n h).app M).val.app U
        (compactSupportQuotientTensor l E W m M U s x))
        (compactSupportQuotientTensor l E W n M U
          ((compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x) := by
  exact quotientTransitionNat_tensor W
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)
    (scalarReductionExtension.{u, u} l E W m)
    (scalarReductionExtension.{u, u} l E W n)
    (compactSupportOrdinaryAdjunction l E W m)
    (compactSupportOrdinaryAdjunction l E W n) M U s x

/-- The balancing transformation has its pure-tensor formula.
Source: ordinary adjunction unit and tensor scalar linearity, Stacks Tag 03EK
(blueprint: lem-coef-compact-support-quotient-module-maps). -/
theorem compactSupportQuotientBalance_formula (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource.{u, u} l E W) (U : W.ProEtᵒᵖ)
      (s : (integralCoefficientCommRingSheaf.{u, u} l E W m).obj.obj U)
      (t : (integralCoefficientCommRingSheaf.{u, u} l E W n).obj.obj U)
      (x : M.val.obj U) :
      ((compactSupportQuotientBalance l E W m n h).hom.app M).val.app U
        (pbcTensorSection (compactSupportLevelSheafQuotient l E W m n h)
        ((scalarReductionExtension l E W m).obj M) U t
          (compactSupportQuotientTensor l E W m M U s x)) =
        compactSupportQuotientTensor l E W n M U
          (t * (compactSupportLevelSheafQuotient l E W m n h).hom.app U s) x := by
  exact quotientBalancing_tensor W
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)
    (scalarReductionExtension.{u, u} l E W m)
    (scalarReductionExtension.{u, u} l E W n)
    (compactSupportOrdinaryAdjunction l E W m)
    (compactSupportOrdinaryAdjunction l E W n) M U s t x

end WeilConjectures
