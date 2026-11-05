/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair

/-! # Native evaluation of the existing signed line powers

Source: Stacks 03EO and 04TT; blueprint Proof (3), evaluation of signed powers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).HasSheafCompose
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
attribute [local instance 2000] cochainModulesMonoidal

/-- Multiplication in degree zero and the actual internal Hom evaluation otherwise.
Source: Stacks 03EO and 04TT (blueprint: lem-pur-signed-line-native-evaluation). -/
def signedLinePairing (L : LineEvaluation.Modules.{uC, vC, r} R) (m : ℤ) (U : Cᵒᵖ) :
    (signedLinePower.{uC, vC, r} L m).val.obj U →
      (signedLinePower.{uC, vC, r} L (-m)).val.obj U → R.obj.obj U :=
  match m with
  | .ofNat 0 => fun a b ↦ (@id (R.obj.obj U) a) * (@id (R.obj.obj U) b)
  | .ofNat (_n + 1) => fun a b ↦ b.app (op (Over.mk (𝟙 U.unop))) a
  | .negSucc _n => fun a b ↦ a.app (op (Over.mk (𝟙 U.unop))) b

end SheafOfModules
