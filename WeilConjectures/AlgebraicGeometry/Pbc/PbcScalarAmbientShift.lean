/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Counit-normalized ambient scalar shift

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-ambient-shift-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section ScalarShift
attribute [local irreducible] completedAdicDerivedChange
variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) (T : Scheme.{u})

private theorem pbcKanCommShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The comparison determines the shift structure by Kan uniqueness, degree by degree.
private theorem pbcRightKanShift_unique
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (F : C ⥤ E) [F.CommShift ℤ] (Q : C ⥤ D) [Q.CommShift ℤ]
    (LF : D ⥤ E) (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift α ℤ)
    (ht : letI := t; NatTrans.CommShift α ℤ) : s = t := by
  have square (q : LF.CommShift ℤ) (hq : letI := q; NatTrans.CommShift α ℤ)
      (n : ℤ) (X : C) :
      LF.map ((Q.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso LF (self := q) n).hom.app (Q.obj X) ≫
            (shiftFunctor E n).map (α.app X) =
        α.app ((shiftFunctor C n).obj X) ≫ (F.commShiftIso n).hom.app X := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α n X
  have he (n : ℤ) : Functor.commShiftIso LF (self := s) n =
      Functor.commShiftIso LF (self := t) n := by
    let H := shiftFunctor E n
    let P := Functor.RightExtension.postcompose₂ Q F H
    let : IsIso (𝟙 (F ⋙ H)) := inferInstance
    let : P.IsEquivalence := by
      dsimp [P, Functor.RightExtension.postcompose₂]
      let a : ((Functor.whiskeringRight D E E).obj H) ⋙
          (Functor.whiskeringLeft C D E).obj Q ⟶
          (Functor.whiskeringLeft C D E).obj Q ⋙
            ((Functor.whiskeringRight C E E).obj H) :=
        { app G := (Functor.associator Q G H).inv }
      let : IsIso a := by apply NatIso.isIso_of_isIso_app
      exact CostructuredArrow.isEquivalenceMap₂ a (𝟙 _)
    let γ := (Functor.associator Q LF H).inv ≫ whiskerRight α H
    have : (LF ⋙ H).IsRightKanExtension γ := by
      constructor
      refine ⟨IsTerminal.ofIso
        (IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
      exact Functor.RightExtension.postcompose₂ObjMkIso H α
    apply Iso.ext
    apply (LF ⋙ H).hom_ext_of_isRightKanExtension γ
    ext X
    simp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app X))).1
    simpa only [Category.assoc] using (square s hs n X).trans (square t ht n X).symm
  exact pbcKanCommShift_ext s t he

set_option linter.unusedVariables false in
/-- Universal tensor counits uniquely fix the termwise derived shift comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-shift-normalization).
Proof: ordinary tensor commutes with cochain shifts, with the identity map on
shifted tensor terms. Its homotopy functor therefore has that comparison.
On flat-term K-flat representatives the universal counit is invertible, so this
comparison descends uniquely and satisfies zero and addition coherence. -/
theorem pbcAmbientScalarShift_exists :
    ∃! q : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ,
      (fun [qInst : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ] ↦
        NatTrans.CommShift (pbcExtensionCounit (pbcScalarCoefficientMap l E F i T)) ℤ)
          (qInst := q) := by
  let φ := pbcScalarCoefficientMap l E F i T
  have := pbcDerivedExtension_universal φ
  have hkan := CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)
    (HomotopyCategory.quasiIso
      (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (.up ℤ))
  have := hkan
  obtain ⟨q, hq⟩ := CategoryTheory.Functor.rightKanExtension_coherentShift _
    DerivedCategory.Qh (pbcDerivedExtend φ) (pbcExtensionCounit φ) hkan
  exact ⟨q, hq, fun q' hq' ↦ pbcRightKanShift_unique _ _ _ _ q' q hq' hq⟩

/-- The tensor shift comparison normalized by its actual derived counit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-shift-normalization). -/
instance pbcAmbientScalarShift : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ :=
  (pbcAmbientScalarShift_exists l E F i T).exists.choose

end ScalarShift
end AlgebraicGeometry.Scheme
