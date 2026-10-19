/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # Simultaneous arithmetic tower resolutions

Source: Stacks Project, Tags 079P and 0941.
-/

@[expose] public section
set_option autoImplicit false
universe a b w uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic

private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }
lemma restriction_preservesKInjectives
    (A : Type a) [Category.{b} A] [Abelian A] (e : ℕ) (he : 1 ≤ e)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((complexRestriction A e).obj I) := by
  let L := (Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).obj (ceilIndex e)
  have adj : L ⊣ restriction A e := (indexAdjunction e he).whiskerLeft (C := A)
  have : L.PreservesHomology := inferInstance
  have := adj.preservesKInjectiveComplexes
  infer_instance
/-- Simultaneous K-injective, degreewise injective tower resolutions.
Source: Stacks Project, Tags 079P and 0941
(blueprint: lem-sp-strict-tower-arithmetic-restriction-resolution).
Resolve in the Grothendieck category of towers. Restriction preserves quasi-isomorphisms
by exactness and preserves K-injectives by its exact left adjoint. -/
theorem strictTowerArithmeticRestrictionResolution
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : limitComplex (ringedSiteModules.{max uC vC r} R) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
        (ComplexShape.up ℤ)))
    (_hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
      (∀ (e : ℕ) (_he : 1 ≤ e) X,
        ∃ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (j : X ⟶ I),
          QuasiIso j ∧ I.IsKInjective ∧ (∀ i : ℤ, Injective (I.X i)) ∧
            CochainComplex.IsKInjective ((complexRestriction _ e).obj I) ∧
            QuasiIso ((complexRestriction _ e).map j)) := by
  classical
  let A := ringedSiteModules.{max uC vC r} R
  have : IsGrothendieckAbelian.{max uC vC r} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{uC, vC, max uC vC r, 0} J R
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint A n).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A n
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{max uC vC r, max uC vC r} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max uC vC r, max uC vC r} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : IsGrothendieckAbelian.{max uC vC r} (ℕᵒᵖ ⥤ A) := {}
  intro e he X
  let I := (CochainComplex.kInjectiveResolutionFunctor.{max uC vC r} (ℕᵒᵖ ⥤ A)).obj X
  let j : X ⟶ I := (CochainComplex.toKInjectiveResolution.{max uC vC r}
    (ℕᵒᵖ ⥤ A)).app X
  have hj : QuasiIso j :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app (ℕᵒᵖ ⥤ A) X).2
  refine ⟨I, j, hj, inferInstance, fun i ↦ inferInstance,
    restriction_preservesKInjectives A e he I, ?_⟩
  infer_instance

end CategoryTheory.StrictTowerArithmetic
