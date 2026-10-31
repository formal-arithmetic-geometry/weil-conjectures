/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorReductionAugmentation
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorChainIdentification

/-! # Identification of tensor reduction comparisons

The reduction comparison is determined by its normalized completion adjunct.
Source: Stacks 07A4, 07A6 and 08TC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open IntegralSystemRealization
attribute [local implicit_reducible] PurCompactSupport.completed
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleRingDerivedPullbackFactors proEtaleTensorPullbackTotalIso
  proEtaleCanonicalTensorComparison Functor.mapDerivedCategory IntegralAmbient.tensorOperationUnit

/-- A normalized change of ordinary tensor models identifies the uniquely specified
reduction comparison with the coefficient calculus comparison.
Source: Stacks 07A4, 07A6 and 08TC.
(blueprint: lem-sf-integral-tensor-reduction-identification).

Proof: transport the strict model's completion augmentation along the normalized
tensor isomorphism. On flat representatives its augmentation is normalized, since
the two strict tensor chains have the same quotient and zero shifted coordinates.
The defining tensor-reduction adjunct equation and the primitive quotient equation
therefore have the same left side. Naturality of the reduction/limit unit transports
the source tensor isomorphism; injectivity of the adjunction Hom equivalence gives
the claimed equality of natural transformations. -/
theorem tensorReduction_eq_normalized (d : RingedModels l E)
    (o : Operations l E) (m : RealizationModel l E o) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (e : (tensorModel l E W).tensor ≅ (d.tensor W).ordinary.tensor)
    (he : ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ)
      (hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) P)
      (hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) Q),
      (tensorModel l E W).representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (d.tensor W).ordinary.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) :
    (tensorReductionComparison l E W).hom =
      Functor.whiskerRight e.hom (pullbackTensorCalculus l E W).reduction ≫
        Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom
          (pullbackTensorCalculus l E W).reduction ≫
        (pullbackTensorCalculus l E W).reductionTensor.hom := by
  let τ := e.hom ≫ (d.tensor W).chi l E
  have hτ : TensorAugmentationNormalized l E W τ := by
    intro P Q
    have h := (d.tensor W).canonical.2 P.obj Q.obj P.property Q.property
    have hh := he P.obj Q.obj P.property Q.property
    change (ConstructibleTensorModel.tensorRepresentativeIso l E W).hom.app (P, Q) ≫
      e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) = _ at hh
    dsimp only [τ, NatTrans.comp_app]
    rw [← Category.assoc, ← Category.assoc, hh]
    simpa only [OpenFactorCoherence.Tensor.chi, NatTrans.comp_app,
      Functor.whiskerLeft_app, ringedTensorChain_eq_constructible l E d W, Category.assoc] using h
  have hb := (tensorReductionAugmentation_existsUnique l E W).exists.choose_spec τ hτ
  have hd := (GeneratorReduction.primitiveQuotientAugmentations l E d o m).1 W
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨M, N⟩
  apply ((pullbackTensorCalculus l E W).adjunction.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  refine (hb M N).symm.trans ?_
  have h := (pullbackTensorCalculus l E W).adjunction.unit.naturality
    (e.hom.app (M, N))
  dsimp only [Functor.id_map, Functor.comp_map] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp]
  rw [← reassoc_of% h]
  simpa only [τ, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ e.hom.app (M, N) ≫ z) (hd M N).2

end WeilConjectures.IntegralOrdinary
