/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackTensorDescent
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackLeftUnitor
import all WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingUnitContraction

/-! # The normalized common-stage unit equation for arbitrary native pullback

Source: Bhatt--Scholze Remark 6.8.15; Stacks Tags 03EK and 0FPT.
(blueprint: lem-sf-native-pullback-unit-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard WeilConjectures.coefficientTotalTensor
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  {R : LocallyFiniteAdicRealization.Realization l X}
  {S : LocallyFiniteAdicRealization.Realization l Y}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {O : Operations l p R S} {A : At l X R} {C : At l Y S}

/-- The tensor equation at the pair of units forces the realization unit equation.
Source: BS Remark 6.8.15 and the monoidal unit coherence laws.
(blueprint: lem-sf-native-pullback-unit-descent).

Proof: instantiate the categorical unit contraction calculation with the two ordinary
realization functors, their common-stage tensors and unitors, native derived pullback,
and the given comparison a. The two realization left-unit laws and the source-unit
normalization supply three faces of the diagram; native derived pullback preserves
its left unitor by its cochain normalization. Insert the tensor equation at the unit
pair and cancel tensoring by the other factor, which is isomorphic to the coefficient
unit. This proves precisely the stated unit equation for the selected source unit. -/
theorem nativePullbackUnitDescent
    (V : TensorComparison l p R S O A C)
    (a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient)
    (u : canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) p)
    (h : NativePullbackTensorEquation l p R S O A C V a
      (pullbackTensorCommonUnit l (PadicAlgCl l) Y)
      (pullbackTensorCommonUnit l (PadicAlgCl l) Y)) :
    (ContinuousRational.derivedPull p O.coefficient).map C.unit.hom ≫
        a.inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) Y) ≫
        (ordinary l X R).map u.exists.choose.hom = V.unit.hom ≫ A.unit.hom := by
  let := A.closed.monoidal
  let := C.closed.monoidal
  exact unit_of_tensor_square
    (commonStageDerivedTensor l (PadicAlgCl l) X)
    (commonStageDerivedTensor l (PadicAlgCl l) Y)
    (pullbackTensorCommonUnit l (PadicAlgCl l) X)
    (pullbackTensorCommonUnit l (PadicAlgCl l) Y)
    (commonStageDerivedPullback l (PadicAlgCl l) p)
    (ordinary l X R) (ordinary l Y S)
    (ContinuousRational.derivedPull p O.coefficient)
    a A.tensor C.tensor V.tensor A.unit C.unit u.exists.choose V.unit
    (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X
      ((commonStageDerivedPullback l (PadicAlgCl l) p).obj
        (pullbackTensorCommonUnit l (PadicAlgCl l) Y)))
    (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) Y
      (pullbackTensorCommonUnit l (PadicAlgCl l) Y))
    (canonicalCommonStagePullbackTensor l (PadicAlgCl l) p
      (pullbackTensorCommonUnit l (PadicAlgCl l) Y)
      (pullbackTensorCommonUnit l (PadicAlgCl l) Y))
    (A.left_unit _) (C.left_unit _) ((u.exists.choose_spec _).1)
    (nativePullbackLeftUnitor l p V _) h

end WeilConjectures.AdicQbarRealization.Proper
