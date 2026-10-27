/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.PodCompletionReindexShifts

/-! # Tensor-factor signed-shift squares under reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The two tensor-factor shift squares commute with a fixed reindexing comparison.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shift-squares).

Proof: on a homogeneous tensor generator, reindexing preserves both degrees and
integer signs. The first-factor square is literal relabelling, while the
second-factor square carries the same Koszul factor on both paths. Generator
extensionality and the normalized Roos model equations descend the identities to
the completed tensor objects and all derived presentations. -/
theorem podReindexingTensorSignedShifts_tensorSquares
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D) (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X) :
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.left M N M' r a).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M' N).hom ≫
          (SX.left ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible M'⟩ r
            ((podOrdinaryReindex l E g).mapIso a ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app M.obj)).hom)) ∧
    (∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
      (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
      ((podOrdinaryReindex l E g).map (SY.right M N N' r b).hom ≫
          ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
        (T.tensor M N').hom ≫
          (SX.right ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩
            ⟨_,T.constructible N'⟩ r
            ((podOrdinaryReindex l E g).mapIso b ≪≫
              ((podOrdinaryReindex l E g).commShiftIso r).app N.obj)).hom)) := by
  sorry

end WeilConjectures
