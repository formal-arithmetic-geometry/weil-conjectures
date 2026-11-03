/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorAssociator

/-! # The integral associator commutes with scalar extension

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The reduction tensor comparisons `pullbackTensorIntegralReductionTensor`, assembled into a
natural isomorphism between reduction of the integral tensor and the system tensor of the
reductions. -/
private def integralReductionTensorIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ integralSystemReduction l E W ≅
      (integralSystemReduction l E W).prod (integralSystemReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, integralSystemReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
        (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
        (((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction) ⋙
          (pullbackTensorCalculus l E W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

/-- The coherently normalized integral associator commutes with the prescribed integral tensor
scalar comparison.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: coherent reduction is fully faithful on the target, so it suffices to compare the
reductions. The coherent scalar-tensor normalization `integralScalarTensorCoherentReduction`
identifies the reduced scalar comparison with the whole-system tensorator, and the defining
reduction equations of both integral associators identify them with the system associators.
The required square of reduced maps is `systemScalarTensorAssociator`. -/
theorem integralAssociatorScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
        (pullbackTensorIntegralAssociator l E W M N P).hom ≫
      (integralTensorScalarComparison l E L ι W M
        ((constructibleIntegralTensor l E W).obj (N, P))).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (𝟙 ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M))
          (integralTensorScalarComparison l E L ι W N P).hom) =
    (integralTensorScalarComparison l E L ι W
        ((constructibleIntegralTensor l E W).obj (M, N)) P).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (integralTensorScalarComparison l E L ι W M N).hom
          (𝟙 ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P))) ≫
      (pullbackTensorIntegralAssociator l L W
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj P)).hom := by
  obtain ⟨p, hp⟩ := integralScalarTensorCoherentReduction l E L ι W
  have := (integralSystemReduction_fullyFaithful l L W).2
  exact reduced_associativity
    (integralSystemReduction l E W) (integralSystemReduction l L W)
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W)
    (integralComparisonDerivedSequenceScalar l E L ι W)
    (constructibleIntegralTensor l E W) (constructibleIntegralTensor l L W)
    (pullbackTensorCalculus l E W).systemClosed.tensor
    (pullbackTensorCalculus l L W).systemClosed.tensor
    (integralReductionTensorIso l E W) (integralReductionTensorIso l L W) p
    (ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W))
    (integralTensorScalarComparison l E L ι W)
    (pullbackTensorIntegralAssociator l E W) (pullbackTensorIntegralAssociator l L W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
    (pullbackTensorCalculus l L W).systemClosed.monoidal.associator
    (fun f g h ↦ @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l L W).systemClosed.monoidal _ _ _ _ _ _ f g h)
    (fun A B C ↦ (pullbackTensorIntegralAssociator_existsUnique l E W A B C).exists.choose_spec)
    (fun A B C ↦ (pullbackTensorIntegralAssociator_existsUnique l L W A B C).exists.choose_spec)
    hp (systemScalarTensorAssociator l E L ι W) M N P

end WeilConjectures
