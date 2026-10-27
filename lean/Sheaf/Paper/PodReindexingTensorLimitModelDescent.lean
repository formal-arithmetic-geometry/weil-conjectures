/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.PodCompletionTensorNormalization
public import Sheaf.Paper.PodReindexingReductionTensorSquare

/-! # Descent of the strict tensor limit model

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
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

/--
The strict normalized tensor equation descends through the product of the two good
complex localizations.  The hypotheses record separately the strict model equation
and its naturality; the conclusion is the component equation used by the parent
limit-model lemma.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC,
0941.  The proof is the fully faithful localization descent after transporting
the strict Roos equation through the two tensor realization isomorphisms.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
-/
theorem podReindexing_tensor_limit_model_descent
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (_hModel : PodCompletedTensorReindex.Model l E g A T)
    (_hNaturality : PodCompletedTensorReindex.Naturality l E g A T)
    (M N : sfIntegralConstructibleCategory l E Y) :
    let q := podReindexingTensorFrame l E g A hA M.obj N.obj
    let t : q.F.obj q.CY ⟶ q.CX := (T.tensor M N).hom
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) =
      t ≫ q.dX.hom := by
  sorry

end WeilConjectures
