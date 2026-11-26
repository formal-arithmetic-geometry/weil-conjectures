/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientOperationsExistence
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenOrdinaryTensorTransport
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenStrictScalarTransport
import WeilConjectures.SmoothPurity.Pur.PurSequenceOrdinaryFactorization
/-! # Ordinary open scalar comparisons

We construct the ordinary slice projection and scalar comparisons for an open immersion, retaining
the strict quotient maps of the ordinary sequence-site factorizations on `X` and `U`.

## Implementation details

The normalized slice tensor formula is transported through the completed coefficient equivalence,
and the strict scalar transport is applied to the two ordinary reductions. Each finite tensor
comparison is obtained by evaluating the strict isomorphism and conjugating by the recorded
evaluations; its scalar-unit normalization supplies the generator field.

## References

* Stacks 0E8I, 03DI, 03DJ, 03EK, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open MonoidalCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.OpenSemilinearTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Retain the ordinary portion of the existing sequence-site factorization. -/
private def reductionOfAdjoints (T : Scheme.{t})
    (A : PurSequenceOrdinaryAdjoints l E T) : OrdinaryReduction l E T where
  functor := A.pullback
  additive := A.pullback_additive
  evaluation := A.tensor
  quotient := A.tensor_transition

private theorem iso_conjugation_cancellation {C : Type*} [Category* C]
    {A B D : C} (e : A ≅ B) (f : A ⟶ D) :
    f = e.hom ≫ e.inv ≫ f := by
  simp only [Iso.hom_inv_id_assoc]

private theorem ordinaryScalarEvaluationComparison_components
    (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
    (a : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
      AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o)
    (M : scalarReductionSource l E U) (n : ℕ) :
    (coefficientSequenceEvaluation l E X n).map (a.hom.app M) ≫
        (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
        (IntegralOpenReduction.finiteExtension l E j o n).map
          ((AU.evaluation n).hom.app M) =
      (AX.evaluation n).hom.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
        (ordinaryScalarEvaluationComparison l E j o AX AU a n).hom.app M := by
  convert iso_conjugation_cancellation
    ((AX.evaluation n).app ((IntegralOpenReduction.extension l E j o).obj M))
    ((coefficientSequenceEvaluation l E X n).map (a.hom.app M) ≫
      (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
        (IntegralOpenReduction.finiteExtension l E j o n).map
          ((AU.evaluation n).hom.app M)) using 1 <;> rfl

/-- For semilinear derived sections whose restriction evaluations are the identity on sections,
there are open coefficient operations, ordinary reductions on `X` and `U`, and ordinary slice
projection and scalar comparisons, with the open systems given by the localization of the
sections and the finite scalar comparisons compatible with the recorded evaluations. -/
theorem openSemilinearOrdinaryComparison
    (sections : SemilinearDerivedSectionsData.{t + 1, t, max u (t + 1)}
      (ProEt.topology X) (IntegralOpenReduction.rings l E X)
      (IntegralOpenReduction.transitions l E X))
    (hsections : ∀ (n : ℕ) N V x,
      HEq ((((sections.localization (IntegralOpenReduction.openObject j)).restrictionEvaluation
        n).hom.app N).val.app V x) x) :
    ∃ (o : Operations l E j) (AX : OrdinaryReduction l E X) (AU : OrdinaryReduction l E U)
      (tc : IntegralOpenReduction.TensorComparison l E j o)
      (μ : OrdinaryTensorComparison l E j o)
      (ordinary : IntegralOpenReduction.extension l E j o ⋙ AX.functor ≅
        AU.functor ⋙ IntegralOpenReduction.systemExtension l E j o),
      o.openSystems = sections.localization (IntegralOpenReduction.openObject j) ∧
      OrdinaryNaturality l E j o μ ∧ OrdinaryGenerators l E j o μ ∧
      (∀ (M : scalarReductionSource l E U) (n : ℕ),
        (coefficientSequenceEvaluation l E X n).map (ordinary.hom.app M) ≫
            (IntegralOpenReduction.extensionEvaluation l E j o n).hom.app (AU.functor.obj M) ≫
            (IntegralOpenReduction.finiteExtension l E j o n).map
              ((AU.evaluation n).hom.app M) =
          (AX.evaluation n).hom.app ((IntegralOpenReduction.extension l E j o).obj M) ≫
            (tc.ordinary n).hom.app M) := by
  obtain ⟨o, ho, hmap⟩ := openCoefficientOperationsExistence l E j sections
  obtain ⟨OX, _⟩ := purSequenceOrdinaryFactorization l E X
  obtain ⟨OU, _⟩ := purSequenceOrdinaryFactorization l E U
  let AX := reductionOfAdjoints l E X OX
  let AU := reductionOfAdjoints l E U OU
  obtain ⟨μ, hμ, hg⟩ := openOrdinaryTensorTransport l E j o hmap
  have hrestriction : ∀ (n : ℕ) N V x,
      HEq ((((o.openSystems.restrictionEvaluation n).hom.app N).val.app V) x) x := by
    simpa only [ho] using hsections
  obtain ⟨ordinary, hordinary⟩ := openStrictScalarTransport l E j o AX AU hrestriction
  let tc : IntegralOpenReduction.TensorComparison l E j o :=
    { ordinary := ordinaryScalarEvaluationComparison l E j o AX AU ordinary
      generators := hordinary }
  exact ⟨o, AX, AU, tc, μ, ordinary, ho, hμ, hg,
    ordinaryScalarEvaluationComparison_components l E j o AX AU ordinary⟩

end WeilConjectures.OpenSemilinearTensor
