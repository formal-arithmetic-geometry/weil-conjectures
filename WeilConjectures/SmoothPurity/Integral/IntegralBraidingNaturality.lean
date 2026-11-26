/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! # Naturality of the integral Koszul braiding

The signed total symmetry of complexes, specialized to the coherently
reduction-normalized completed integral tensor, is natural in both inputs.

## References

* Stacks Project, Cohomology on Sites, Tag 0FPQ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

private def completedBraidingNat_R4
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    integralCompletedTensor l E W ≅
      pullbackTensorSwap _ ⋙ integralCompletedTensor l E W :=
  (pullbackTensorIntegralTensorModel l E W) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction)
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel))
      (coefficientSequenceLimit l E W) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorSwap _)
      (pullbackTensorIntegralTensorModel l E W).symm

private theorem completedBraiding_normalization_R4
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorIntegralBraiding l E W M N).hom.hom =
      (completedBraidingNat_R4 l E W).hom.app (M.obj, N.obj) := by
  let e : (constructibleIntegralTensor l E W).obj (M, N) ≅
      (constructibleIntegralTensor l E W).obj (N, M) :=
    ObjectProperty.isoMk _ ((completedBraidingNat_R4 l E W).app (M.obj, N.obj))
  have he : (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        (pullbackTensorIntegralReductionTensor l E W N M).hom =
      (pullbackTensorIntegralReductionTensor l E W M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj) := by
    dsimp only [e, completedBraidingNat_R4, ObjectProperty.isoMk, ObjectProperty.homMk,
      pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.mapIso_hom, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [← Category.assoc
      ((pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).inv.app (N.obj, M.obj)))
      ((pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).hom.app (N.obj, M.obj))),
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun k ↦
      (pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).hom.app (M.obj, N.obj)) ≫ k)
      ((pullbackTensorCalculus l E W).adjunction.counit.naturality _)
  have h := (pullbackTensorIntegralBraiding_existsUnique l E W M N).unique
    ((pullbackTensorIntegralBraiding_existsUnique l E W M N).exists.choose_spec) he
  exact congrArg (fun i ↦ i.hom.hom) h

/-- The coherently normalized integral Koszul braiding is natural in both inputs. -/
theorem pullbackTensorIntegralBraiding_naturality
    (M M' N N' : sfIntegralConstructibleCategory l E W)
    (a : M ⟶ M') (b : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom a b) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom b a) := by
  apply ObjectProperty.hom_ext
  change (integralCompletedTensor l E W).map (Prod.mkHom a.hom b.hom) ≫ _ =
    _ ≫ (integralCompletedTensor l E W).map (Prod.mkHom b.hom a.hom)
  rw [completedBraiding_normalization_R4, completedBraiding_normalization_R4]
  exact (completedBraidingNat_R4 l E W).hom.naturality (Prod.mkHom a.hom b.hom)

end WeilConjectures
