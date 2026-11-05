/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionAssociationSuccessor

/-! # Ordinary association of strict scalar tensor complexes

Source: Stacks 03D7, 03EK and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private theorem conjugateSection
    {S₀ S₁ D₀ D₁ T₀ T₁ : Type*}
    (a₀ : S₀ → T₀) (a₁ : S₁ → T₁) (ai₀ : T₀ → S₀)
    (d₁ : D₁ → T₁) (di₀ : T₀ → D₀) (di₁ : T₁ → D₁)
    (s : S₁ → S₀) (d : D₁ → D₀) (t : T₁ → T₀) (x : S₁)
    (ht : d (di₁ (a₁ x)) = di₀ (t (d₁ (di₁ (a₁ x)))))
    (hs : s x = ai₀ (t (a₁ x)))
    (hd : d₁ (di₁ (a₁ x)) = a₁ x) (ha : a₀ (ai₀ (t (a₁ x))) = t (a₁ x)) :
    d (di₁ (a₁ x)) = di₀ (a₀ (s x)) := by
  rw [ht, hd, hs, ha]

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

section Glue
attribute [local irreducible] coefficientSequenceCommRingSheaf integralCoefficientSheaf
  completedIntegralCoefficientSheafUnrestricted

end Glue

attribute [local irreducible] integralScalarReduction

end WeilConjectures
