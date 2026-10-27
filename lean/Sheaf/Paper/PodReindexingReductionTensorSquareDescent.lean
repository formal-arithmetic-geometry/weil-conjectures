/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.PodCompletionReindexModels
public import Sheaf.Paper.PodReindexingCoherenceData
public import Sheaf.Paper.CompletedPullbackTowerRealizations
import all Sheaf.Paper.CompletedPullbackTowerCore

/-! # Descent of the strict reduction/tensor representative square

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent)
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
The strict pure-tensor calculation descends through the two K-flat localizations.
The hypothesis is the comparison's sectionwise pure-tensor formula; the conclusion
is the whole-system square after the reduction and system tensor maps.  The descent
uses the quotient-generator and transition laws of `A`, the normalized system
comparison, and full faithfulness of the product localization.  It is stated
separately so that the representative calculation is not hidden in the derived
square theorem.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: lem-pod-reindexing-reduction-tensor-square-descent).
-/
theorem podReindexing_reduction_tensor_square_descent
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (w : (podReindexCalculus l E Y).systemClosed.tensor ⋙
        integralComparisonDerivedSequencePullback l E g ≅
      (integralComparisonDerivedSequencePullback l E g).prod
        (integralComparisonDerivedSequencePullback l E g) ⋙
          (podReindexCalculus l E X).systemClosed.tensor)
    (v : ∀ M N : podReindexingDerived l E Y none,
      (podOrdinaryReindex l E g).obj
          ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N)) ⟶
        (podReindexCalculus l E X).integralClosed.tensor.obj
          ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N))
    (hPure : ∀ (P L : PodReindexingCoherence.K l E Y none) (p q k : ℤ)
      (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((c.tensorChain P L).hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Y) (podReindexingRing l E Y none) P L p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) (podReindexingRing l E X none)
        ((podReindexingComplexFunctor l E g none).obj P)
        ((podReindexingComplexFunctor l E g none).obj L) p q k hk
        (op U) x y)
    (M N : podReindexingDerived l E Y none) :
    (integralComparisonDerivedSequencePullback l E g).map
        ((podReindexCalculus l E Y).reductionTensor.hom.app (M, N)) ≫
      w.hom.app ((podReindexCalculus l E Y).reduction.obj M,
        (podReindexCalculus l E Y).reduction.obj N) ≫
      (podReindexCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (A.reduction.hom.app M) (A.reduction.hom.app N)) =
    A.reduction.hom.app
        ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N)) ≫
      (podReindexCalculus l E X).reduction.map (v M N) ≫
      (podReindexCalculus l E X).reductionTensor.hom.app
        ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N) := by
  sorry

end WeilConjectures
