/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete

set_option linter.privateModule false

/-! The integral constructible proper heart estimate. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem complete_upper_of_levels
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (Y : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules ℓ E Y))
    (hK : IsDerivedComplete ℓ E Y K) (b : ℤ)
    (hb : ∀ n : ℕ, (AdicCompletion.integralLevel ℓ E Y K n).IsLE b) :
    K.IsLE (b + 1) := by
  obtain ⟨P, hP, ⟨e⟩, hcomplete⟩ := hK
  obtain ⟨p, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit ℓ E Y K P hP e
  have : IsIso (AdicCompletion.completionMap ℓ E Y K P e) := by
    dsimp [AdicCompletion.completionMap]
    infer_instance
  have hprod : (∏ᶜ AdicCompletion.integralLevel ℓ E Y K).IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro q hq
    have hP := isLimitOfPreserves (DerivedCategory.homologyFunctor _ q)
      (productIsProduct (AdicCompletion.integralLevel ℓ E Y K))
    apply (IsZero.iff_id_eq_zero _).2
    apply hP.hom_ext
    intro n
    exact (DerivedCategory.isZero_of_isLE _ b q hq (hX := hb n.as)).eq_of_tgt _ _
  have hprod' : (∏ᶜ AdicCompletion.integralLevel ℓ E Y K).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE_of_le _ b (b + 1) (by omega)
  have hshift : ((∏ᶜ AdicCompletion.integralLevel ℓ E Y K)⟦(-1 : ℤ)⟧).IsLE
      (b + 1) := DerivedCategory.TStructure.t.isLE_shift _ b (-1) (b + 1) (by omega)
  have hroos : (DerivedCategory.Q.obj (AdicCompletion.roos ℓ E Y P)).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE₂ _ (inv_rot_of_distTriang _ hT)
      (b + 1) hshift hprod'
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (asIso (AdicCompletion.completionMap ℓ E Y K P e)).symm (b + 1)

end AlgebraicGeometry.ProEtale
