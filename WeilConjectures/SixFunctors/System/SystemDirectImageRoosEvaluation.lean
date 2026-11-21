/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.System.SystemDirectImageRoosExistence
import WeilConjectures.SixFunctors.System.SystemDirectImageReductionNormalized
import WeilConjectures.SixFunctors.Sf.SfDirectImageRoosFiniteReduction
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Finite evaluation of the direct-image Roos object

This is the projection and finite-evaluation part of the direct-image Roos
comparison.  The object and its comparison isomorphism are parameters; the
statement supplies the simultaneously normalized finite evaluation
isomorphisms and their actual projection equations.

## References

* [Stacks, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
* Zheng, Construction 4.1, Lemma 4.10
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite evaluations of a chosen direct-image Roos object are compatible with
the actual total-limit projections. -/
theorem systemDirectImage_roosEvaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    [HasProduct (sfDirectImageTerm l E f K)]
    (L : SfIntegralDirectImage l E f K)
    (e : (coefficientSequenceLimit l E Y).obj
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        (S.reduction.obj K)) ≅ L.obj) :
    ∃ a : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E Y n).obj
        ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
          (S.reduction.obj K)) ≅ sfFiniteDerivedDirectImage l E f K n,
      ∀ n : ℕ,
        (coefficientSequenceProjection l E Y n).app
            ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
              (S.reduction.obj K)) ≫
          (coefficientFiniteDerivedRestriction l E Y n).map (a n).hom =
        e.hom ≫ L.projection ≫ Pi.π (sfDirectImageTerm l E f K) n := by
  obtain ⟨T, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
    (S.reduction.obj K)
  have hN : IsNormalizedCoefficientSequence l E Y N :=
    systemDirectImage_reduction_normalized l E f S K
  have hc : IsIso (T.adjunction.counit.app N) :=
    ((purNormalizedReconstructionOfScheme l E Y T).1 N hN).2
  let q (n : ℕ) := ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).symm
    ((coefficientSequenceProjection l E Y n).app N)
  have hq (n : ℕ) : IsIso (q n) := by
    have heq : q n = (T.reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map (T.adjunction.counit.app N) := by
      apply ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).injective
      exact ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).apply_symm_apply _
        |>.trans (T.counit_projection N n).symm
    rw [heq]
    infer_instance
  have hr (n : ℕ) : IsIso (sfDirectImageReductionComparison l E f L n) :=
    sfDirectImageRoos_finiteReduction l E f K L n
  let a (n : ℕ) := (asIso (q n)).symm ≪≫
    (coefficientFiniteDerivedExtension l E Y n).mapIso e ≪≫
      asIso (sfDirectImageReductionComparison l E f L n)
  refine ⟨a, ?_⟩
  intro n
  let adj := coefficientFiniteAdjunction l E Y n
  have hqa : q n ≫ (a n).hom =
      (coefficientFiniteDerivedExtension l E Y n).map e.hom ≫
        sfDirectImageReductionComparison l E f L n := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Functor.mapIso_hom, IsIso.hom_inv_id_assoc]
  calc
    _ = (adj.homEquiv _ _) (q n ≫ (a n).hom) := by
      rw [adj.homEquiv_naturality_right]
      simp only [q, adj, Equiv.apply_symm_apply]
      rfl
    _ = (adj.homEquiv _ _)
        ((coefficientFiniteDerivedExtension l E Y n).map e.hom ≫
          sfDirectImageReductionComparison l E f L n) := congrArg _ hqa
    _ = _ := by
      rw [adj.homEquiv_naturality_left]
      exact congrArg (fun z ↦ e.hom ≫ z)
        (((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv
          L.obj (sfFiniteDerivedDirectImage l E f K n)).apply_symm_apply _)

end WeilConjectures
