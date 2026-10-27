/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.PodCompletionTensorNormalization
public import Sheaf.Paper.PodReindexingEvaluationShiftComposition

/-! # Tensor augmentation under normalized reindexing

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 2 and 4;
Stacks 07A4, 08J9, 099B and 099M (blueprint: lem-pod-reindexing-tensor-augmentation-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary-to-completed tensor augmentation commutes with the two normalized
reindexing tensor maps. The parameter η is fixed by its displayed defining equation.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 099M
(blueprint: lem-pod-reindexing-tensor-augmentation-square).

Proof: take simultaneous flat-term K-flat representatives of M and L. The ordinary
reindexing tensor map sends each homogeneous x tensor y to Fx tensor Fy. Reduction
sends this generator to its two quotient reductions, and the completed tensor map
has exactly this formula by Generators and Model. The tensor augmentation is the
actual reduction adjunction unit, followed by reductionTensor and the normalized
Roos tensor comparison. The Unit law transports its first factor; the quotient
formulas transport its second factor. On both Roos product coordinates the two
composites are the same diagonal relabelling, by RoosFst and RoosSnd. Thus the
augmentation square commutes on representatives, including all quotient arrows.
The representative localizations and their naturality descend this equality to
M and L. The equality h only identifies the two projection-fixed presentations;
equality proofs give the same eqToIso by proof irrelevance. No completeness of
the ordinary tensor or finite Tor dimension is used. -/
theorem podReindexing_tensor_augmentation_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (η : ∀ (W : Scheme.{u}) (M L : podReindexingDerived l E W none),
      (podReindexCalculus l E W).integralClosed.tensor.obj (M, L) ⟶
        (integralCompletedTensor l E W).obj (M, L))
    (hη : η = fun W M L ↦
      (podReindexCalculus l E W).adjunction.unit.app
        (@MonoidalCategoryStruct.tensorObj _ _
          (podReindexCalculus l E W).integralClosed.monoidal.toMonoidalCategoryStruct M L) ≫
      (coefficientSequenceLimit l E W).map
        ((podReindexCalculus l E W).reductionTensor.hom.app (M, L)) ≫
      (pullbackTensorIntegralTensorModel l E W).inv.app (M, L))
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :
    ∀ M L : sfIntegralConstructibleCategory l E Y,
      (podOrdinaryReindex l E g).map (η Y M.obj L.obj) ≫ (T.tensor M L).hom =
        (((eqToIso h).app
          ((podReindexCalculus l E Y).integralClosed.tensor.obj (M.obj, L.obj))).symm ≪≫
          c.tensor.app (M.obj, L.obj) ≪≫
          (podReindexCalculus l E X).integralClosed.tensor.mapIso
            (((eqToIso h).app M.obj).prod ((eqToIso h).app L.obj))).hom ≫
          η X ((podOrdinaryReindex l E g).obj M.obj)
            ((podOrdinaryReindex l E g).obj L.obj) := by sorry

end WeilConjectures
