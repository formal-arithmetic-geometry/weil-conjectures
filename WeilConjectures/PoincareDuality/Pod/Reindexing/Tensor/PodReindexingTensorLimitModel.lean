/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorLimitModelDescent

/-! # Limit realization of the normalized completed tensor reindexing

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed tensor comparison is the limit of the coherent system tensor map.
This identifies isomorphisms only; no ordinary tensor comparison or augmentation occurs.
Source: Stacks 07A4, 08TC, 0941. -/
theorem podReindexing_tensor_limit_model
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (M N : sfIntegralConstructibleCategory l E Y) :
    let q := podReindexingTensorFrame l E g A hA M.obj N.obj
    let t : q.F.obj q.CY ⟶ q.CX := (T.tensor M N).hom
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫ q.RX.map q.w₂ =
      t ≫ q.dX.hom := by
  have h := podReindexing_tensor_limit_model_descent l E g A T hA
    hT.1 hT.2.2.2.2.1 hT.2.2.2.1 M N
  simpa only [Functor.map_comp, Category.assoc] using h

end WeilConjectures
