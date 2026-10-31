/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSignedTwistProducts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorOrdinaryAdditionFrame
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorOrdinaryAdditionFrameExt
/-! # Ordinary scalar extension and finite signed multiplication -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting
/-- Ordinary adjuncts of the specified semilinear line maps preserve signed products.
Source: finite reduction of purity, Step 2, expanded parent Step 5; Stacks Project
Tags 03EK, 04TT and 03EM.
(blueprint: lem-pur-finite-tensor-ordinary-addition).
Proof: form the two displayed maps after transposing the ordinary adjuncts. The
frame calculation is the signed-line comparison, realization-pure, and normalized
product calculation on one coherent generator. The frame-extensionality lemma
extends it to the entire fixed tensor. Finally injectivity of the adjunction
hom-equivalence identifies the transposed equality with the displayed equality.
Thus zero, positive, negative and mixed exponents are handled uniformly by the
signed-line product theorem rather than by sign case splitting. -/
theorem finiteTensorOrdinaryAddition (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (r t : ℤ) :
    let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
    let E := ProEtale.sheafExtendScalars φ T
    let a := ProEtale.sheafExtendScalarsAdjunction φ T
    let c := P.finiteTensorLineMaps m hm hmn T
    let d := fun k : ℤ ↦ (a.homEquiv _ _).symm
      (P.finiteTensorFixedLineMap m hm hmn T c k)
    E.map (P.finiteTensorSheafProducts T r t).hom ≫ d (r + t) =
      Functor.OplaxMonoidal.δ E
        (P.finiteTensorFixedSheaf T r) (P.finiteTensorFixedSheaf T t) ≫
      (d r ⊗ₘ d t) ≫
        ((P.finiteReductionSetting m hm).finiteTensorSheafProducts T r t).hom := by
  dsimp
  let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  let E := ProEtale.sheafExtendScalars φ T
  let a := ProEtale.sheafExtendScalarsAdjunction φ T
  let c := P.finiteTensorLineMaps m hm hmn T
  let d := fun k : ℤ ↦ (a.homEquiv _ _).symm
    (P.finiteTensorFixedLineMap m hm hmn T c k)
  let f := a.homEquiv _ _
    (E.map (P.finiteTensorSheafProducts T r t).hom ≫ d (r + t))
  let g := a.homEquiv _ _
    (Functor.OplaxMonoidal.δ E (P.finiteTensorFixedSheaf T r)
      (P.finiteTensorFixedSheaf T t) ≫ (d r ⊗ₘ d t) ≫
      ((P.finiteReductionSetting m hm).finiteTensorSheafProducts T r t).hom)
  have hfg : f = g := by
    apply finiteTensorOrdinaryAddition_frame_ext P m hm hmn T r t f g
    intro V e x y hx hy
    change (a.homEquiv _ _
        (E.map (P.finiteTensorSheafProducts T r t).hom ≫ d (r + t))).hom.app
          (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y) =
      (a.homEquiv _ _
        (Functor.OplaxMonoidal.δ E (P.finiteTensorFixedSheaf T r)
          (P.finiteTensorFixedSheaf T t) ≫ (d r ⊗ₘ d t) ≫
          ((P.finiteReductionSetting m hm).finiteTensorSheafProducts T r t).hom)).hom.app
          (Opposite.op V) (P.finiteTensorSectionTmul T r t V x y)
    exact finiteTensorOrdinaryAddition_frame P m hm hmn T r t V e x y hx hy
  apply (a.homEquiv _ _).injective
  change f = g
  exact hfg
end WeilConjectures.PurityFiniteSetting
