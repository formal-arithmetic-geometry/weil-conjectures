/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.CoefficientNormalizedReductionModels

/-! # Internal-Hom fibers of normalized coefficient systems

Source: Stacks 07A4, 08J9, 0A95 and 0941; semilinear finite-prefix adjunction
(blueprint: lem-coef-normalized-internal-hom-fibers).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Preservation of internal composition for an evaluation-defined comparison.
Source: Stacks 08J9, 0A98
(blueprint: lem-coef-normalized-internal-hom-fibers). -/
def CoefficientInternalHomComposition
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
          (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
            (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

attribute [local irreducible] CoefficientInternalHomComposition

/-- The local Hom comparisons, without any global-sections data.
Source: Stacks 08J9, 0A95 and 0941
(blueprint: lem-coef-normalized-internal-hom-fibers). -/
structure CoefficientNormalizedInternalHomFibers
    (R : CoefficientDerivedSystemReduction l E W)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) where
  /-- Reduction preserves internal composition as a system map. -/
  reduction_composition : CoefficientInternalHomComposition R.integralClosed R.systemClosed
    R.reduction R.reductionTensor
  /-- Finite scalar comparison preserves internal composition. -/
  finite_composition : ∀ n : ℕ, CoefficientInternalHomComposition
    R.integralClosed (R.finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n)
  /-- Internal Hom on normalized inputs has exactly the finite internal-Hom fibers. -/
  fiberHom : ∀ (M N : coefficientSequenceDerived l E W),
    IsNormalizedCoefficientSequence l E W M → IsNormalizedCoefficientSequence l E W N →
    ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≅
        (coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientSequenceDerivedEvaluation l E W n).obj M),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The fiber identification is induced by simultaneous system evaluation. -/
  fiber_evaluation : ∀ (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ),
    (R.evaluationTensor n).inv.app
        ((coefficientSequenceInternalHom l E W).obj (op M, N), M) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (R.systemClosed.evaluation M N) =
    (R.finiteClosed n).tensor.map
        (Prod.mkHom ((fiberHom M N hM hN n).hom) (𝟙 _)) ≫
      (R.finiteClosed n).evaluation
        ((coefficientSequenceDerivedEvaluation l E W n).obj M)
        ((coefficientSequenceDerivedEvaluation l E W n).obj N)
  /-- The adjunct of the actual `coefficientSequenceDerivedTransition` on internal Hom,
  under `fiberHom` at m and n, is c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
  Here c_(m,n) transposes reduced finite evaluation using `Q.tensor`,
  whose `tensor_model` fixes its comparison on every pair of K-flat representatives. -/
  fiber_transition : CoefficientFiberTransition l E W R.toCoefficientDerivedSystemTensors
    Q fiberHom
/-- Normalized reduction and quotient models give the local internal-Hom calculus.
Source: Stacks, sites-cohomology.tex, Tags 07A4, 08J9, 0A95 and 0941;
resolution-model construction, step 3
(blueprint: lem-coef-normalized-internal-hom-fibers).

Proof:
Use semilinearDerivedSections for the actual finite coefficient sequence. Compare its
scalar-extension adjunctions with Q.adjunction via the normalized ordinary units and
derived counits. Both compute the same derived restriction functors. Thus their
cartesian condition is exactly IsNormalizedCoefficientSequence. Its finite-prefix
left extension adjoint to evaluation, and the tensor projection formula for that
extension, give the internal-Hom fiber isomorphism for normalized first input.
Transpose its evaluation equation to identify that isomorphism with the one for
R.systemClosed and R.finiteClosed: their tensor models fix the same ordinary
uncurrying on K-flat/K-injective representatives. Applying the semilinear HomReductionFormula,
with Q.tensor_model identifying its reduced evaluation map, gives fiber_transition.
Use ringedPullbackHomEvaluationComparison for reduction and for each scalar extension.
Their canonical tensor maps agree with R.reductionTensor and R.finiteTensor by the
representative normalizations. The supplied associator models in hT identify their
monoidal coherence with the signed total-complex coherence. This gives
reduction_composition and finite_composition.
This construction uses no global sections or comparison with a total limit. -/
theorem coefficientNormalizedInternalHomFibers
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :
    Nonempty (CoefficientNormalizedInternalHomFibers l E W R Q) := by sorry

end WeilConjectures
