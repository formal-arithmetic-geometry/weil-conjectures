/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Sheaf.Paper.ScalarExtensionTowerRealizationData
import Sheaf.Paper.ScalarTowerPullbackStrictSquare

/-! # From the strict square to normalized total-limit coordinates

Source: Stacks 07A4 and 0941; realization step 8 of
lem-pur-scalar-extension-tower-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The normalized representative and Roos-limit assembly.
Assuming the strict quotient square, the normalization fields of `SX` and `SY`
identify its two strict routes with the displayed realization maps.  Naturality
of the normalized Roos bridge then gives the target equation.  This is the
remaining assembly step after `scalarTowerPullbackStrictSquare`; its proof is
independent of the generator calculation.
Source: Stacks 07A4 and 0941
(blueprint: stage3-pur-scalar-pullback-limit-bridge).
Proof: choose a coherent K-flat quotient presentation, apply both normalization
fields, use Roos naturality, and cancel the inverse system isomorphism.
-/
theorem scalarTowerPullbackLimitSquare_mate (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ML : CompletedOperations.Models.{u, u} l L W)
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true)
      (ME.calculus true) (ML.roos true))
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false)
      (ME.calculus false) (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (M : sfIntegralConstructibleCategory l E (W false))
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj M.obj))
    (_hstrict : leftRoute l E L ι f = rightRoute l E L ι f) :
    ((scalarPullbackCompleted l E L ι f M.obj M.property.1 hF).hom ≫
        (ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequencePullback.{u, u} l L f).map
            (scalarReduction l E L ι (W false) (ME.calculus false) (ML.calculus false)
              (ML.roos false) SY M.obj)) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          ((ME.calculus false).reduction.obj M.obj))) =
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj M.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
            (pullbackReduction l E W ME f M.obj) ≫
          (integralComparisonSystemScalarPullback.{u, u} l E L ι f).hom.app
            ((ME.calculus false).reduction.obj M.obj))) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          ((ME.calculus false).reduction.obj M.obj)) := by
  sorry

end WeilConjectures.ScalarExtensionTower
