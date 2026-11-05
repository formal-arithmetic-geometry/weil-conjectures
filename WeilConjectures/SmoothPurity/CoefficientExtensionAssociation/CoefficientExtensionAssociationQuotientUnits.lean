/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # Quotient unit sections of an ordinary tensor system

Source: Stacks 03CZ and 03D7; the sequence site preceding 0941.
All constructions are actual normalized adjunction units. The generic laws prevent
kernel checking from expanding the completed coefficient ring at each application.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace CoefficientExtensionAssociation
section GenericLaw
universe a b c v₁ v₂ v₃

universe d e r₀
/-- The actual adjunction unit section, returned in the native target module.
Keeping this carrier explicit avoids unfolding restriction-of-scalars actions.
Source: Stacks 03D7. -/
@[irreducible] def normalizedUnitSection
    {C : Type d} [Category.{e} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r₀}} (f : R ⟶ S)
    {F : SheafOfModules.{r₀} R ⥤ SheafOfModules.{r₀} S}
    (adj : F ⊣ SheafOfModules.restrictScalars f)
    (M : SheafOfModules.{r₀} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (adj.unit.app M).val.app U x

end GenericLaw

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

attribute [local irreducible] quotientAdjunction

/-- The normalized quotient tensor unit section.
Source: Stacks 03CZ and 03D7. -/
@[irreducible] def finiteUnitSection (M : scalarReductionSource l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarReductionExtension l E W n).obj M).val.obj U :=
  normalizedUnitSection (coefficientProjection l E W n) (quotientAdjunction l E W n) M U x

/-- The quotient unit transported into the supplied ordinary system model.
Source: Stacks 03D7 and the sequence-site construction preceding 0941. -/
@[irreducible] def quotientUnitSection (M : CompletionUnit.OrdinaryModel l E W)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    ((coefficientSequenceEvaluation l E W n).obj (M.tensor.obj K)).val.obj U :=
  ((M.evaluation n).inv.app K).val.app U (finiteUnitSection l E W K n U x)

end CoefficientExtensionAssociation
end WeilConjectures
