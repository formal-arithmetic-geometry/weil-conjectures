/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.CoefficientNormalizedReductionModels

/-! # Forward coherence of normalized tensor comparisons

Source: Stacks 07A4 and 08J9; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-associativity-hom).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The forward tensorator associativity equation.
Source: Stacks 07A4; this is the strong monoidal coherence equation whose inverse
form is used by `CoefficientTensorAssociativity`.
(blueprint: lem-coef-normalized-tensor-associativity-hom).

Proof: choose simultaneous flat-term K-flat representatives and use the prescribed
pairwise normalization squares to identify every tensorator with its ordinary
pure-tensor chain map.  The signed total-tensor associator sends each triple pure
tensor to the same reassociated tensor.  Equality on coproduct generators gives the
chain-map equality, and localization and naturality transport it to all derived
objects.  The same construction applies to every finite coefficient level. -/
def CoefficientTensorHomAssociativity
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.monoidal.associator P Q V).hom ≫
        μ.hom.app (P, SA.tensor.obj (Q, V)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (μ.hom.app (Q, V))) =
      μ.hom.app (SA.tensor.obj (P, Q), V) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (P, Q)) (𝟙 (F.obj V))) ≫
        (SB.monoidal.associator (F.obj P) (F.obj Q) (F.obj V)).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Forward coherence for the fixed reduction and finite tensor comparisons.
(blueprint: lem-coef-normalized-tensor-associativity-hom). -/
theorem coefficientNormalizedTensorAssociativityHom
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    CoefficientTensorHomAssociativity R.integralClosed R.systemClosed R.reduction
        R.reductionTensor ∧
      ∀ n : ℕ, CoefficientTensorHomAssociativity R.integralClosed (R.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) := by sorry

end WeilConjectures
