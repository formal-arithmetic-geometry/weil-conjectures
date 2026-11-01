/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons

/-! # Intrinsic realization of the finite tensor-source comparison

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2.
(blueprint: def-pur-finite-reduction-tensor-source)

The comparison uses scalar realization, the tensorator, the specified pullback
mate and the positive line comparison. It uses no purity morphism or orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The canonical comparison between the two inverse-realized reduced inputs.
Source: blueprint reduction Step 2, scalar realization
(blueprint: def-pur-finite-reduction-tensor-source). -/
def finiteReductionTensorInputComparison (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (Y : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteTensorReduction m hm hmn Y).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) ≅
      (Scheme.sfIntrinsicDerivedEquivalence Y (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReduction m hm hmn Y).obj K) :=
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let E' := Scheme.sfIntrinsicDerivedEquivalence Y (P.finiteReductionSetting m hm).Ring
  E'.functor.preimageIso
    ((ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) Y).symm.app (E.inverse.obj K) ≪≫
      (P.finiteReduction m hm hmn Y).mapIso (E.counitIso.app K) ≪≫
      (E'.counitIso.app ((P.finiteReduction m hm hmn Y).obj K)).symm)

/-- The reduction comparison on the tensor source before reassociation.
Source: blueprint reduction Step 2, tensor and line comparisons
(blueprint: def-pur-finite-reduction-tensor-source). -/
def finiteReductionTensorSourceComparison (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] (f : X ⟶ Y) (d : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
          (P.smoothPurityTensorSource f d K)) ≅
      (Scheme.sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring).functor.obj
        ((P.finiteReductionSetting m hm).smoothPurityTensorSource f d
          ((P.finiteReduction m hm hmn Y).obj K)) :=
  let E := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let E' := Scheme.sfIntrinsicDerivedEquivalence X (P.finiteReductionSetting m hm).Ring
  let Q := P.finiteReductionSetting m hm
  (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X).app (P.smoothPurityTensorSource f d K) ≪≫
    E'.functor.mapIso
      (P.finiteTensorPurityTargetComparison m hm hmn f d (E.inverse.obj K)) ≪≫
    E'.functor.mapIso
      (((smoothPurityTensor Q.Coefficient X).mapIso
        ((Q.smoothPurityPullback f).mapIso
          (P.finiteReductionTensorInputComparison m hm hmn Y K))).app (Q.diagonalTwist X d))

end WeilConjectures.PurityFiniteSetting
