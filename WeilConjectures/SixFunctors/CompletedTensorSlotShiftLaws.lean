/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOperationShiftData
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.CompletedTensorShiftAddOnGood

/-! # Shift laws for both prescribed completed tensor slots

Source: Stacks 011G, 014E, 06YU, 0FPQ and 0FNH; the maps-used sentence of
blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor

namespace WeilConjectures.IntegralSystemRealization

private theorem shiftZero_of_add {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)
    (s : ∀ r : ℤ, shiftFunctor C r ⋙ F ≅ F ⋙ shiftFunctor D r)
    (hadd : ∀ a b, s (a + b) = CommShift.isoAdd (s a) (s b)) :
    s 0 = CommShift.isoZero F ℤ := by
  have hu : CommShift.isoAdd (CommShift.isoZero F ℤ) (s 0) = s 0 :=
    CommShift.isoZero_isoAdd'_ (s 0)
  have h : CommShift.isoAdd (s 0) (s 0) =
      CommShift.isoAdd (CommShift.isoZero F ℤ) (s 0) := (hadd 0 0).symm.trans hu.symm
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (shiftFunctor D (0 : ℤ)).map_injective
  have hx := NatTrans.congr_app (congrArg Iso.hom h) X
  simp only [CommShift.isoAdd_hom_app] at hx
  have hx' := (cancel_epi (F.map ((shiftFunctorAdd C 0 0).hom.app X))).mp hx
  have hx'' := (cancel_epi ((s 0).hom.app ((shiftFunctor C 0).obj X))).mp hx'
  exact (cancel_mono ((shiftFunctorAdd D 0 0).inv.app (F.obj X))).mp hx''

private def firstSlotAdd {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : tensorShiftFirst C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : tensorShiftFirst C b ⋙ F ≅ F ⋙ shiftFunctor C b) :
    tensorShiftFirst C (a + b) ⋙ F ≅ F ⋙ shiftFunctor C (a + b) :=
  isoWhiskerRight
      (NatIso.prod (shiftFunctorAdd C a b) (Functor.leftUnitor (𝟭 C)).symm) F ≪≫
    isoWhiskerLeft (tensorShiftFirst C a) sb ≪≫
    isoWhiskerRight sa (shiftFunctor C b) ≪≫
    isoWhiskerLeft F (shiftFunctorAdd C a b).symm

private theorem firstSlotAdd_hom_app {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : tensorShiftFirst C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : tensorShiftFirst C b ⋙ F ≅ F ⋙ shiftFunctor C b) (M N : C) :
    (firstSlotAdd F a b sa sb).hom.app (M, N) =
      F.map ((shiftFunctorAdd C a b).hom.app M, 𝟙 N) ≫
        sb.hom.app (M⟦a⟧, N) ≫ (shiftFunctor C b).map (sa.hom.app (M, N)) ≫
        (shiftFunctorAdd C a b).inv.app (F.obj (M, N)) := rfl

private def secondSlotAdd {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : completedTensorShiftSecond C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : completedTensorShiftSecond C b ⋙ F ≅ F ⋙ shiftFunctor C b) :
    completedTensorShiftSecond C (a + b) ⋙ F ≅ F ⋙ shiftFunctor C (a + b) :=
  isoWhiskerRight
      (NatIso.prod (Functor.leftUnitor (𝟭 C)).symm (shiftFunctorAdd C a b)) F ≪≫
    isoWhiskerLeft (completedTensorShiftSecond C a) sb ≪≫
    isoWhiskerRight sa (shiftFunctor C b) ≪≫
    isoWhiskerLeft F (shiftFunctorAdd C a b).symm

private theorem secondSlotAdd_hom_app {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : completedTensorShiftSecond C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : completedTensorShiftSecond C b ⋙ F ≅ F ⋙ shiftFunctor C b) (M N : C) :
    (secondSlotAdd F a b sa sb).hom.app (M, N) =
      F.map (𝟙 M, (shiftFunctorAdd C a b).hom.app N) ≫
        sb.hom.app (M, N⟦a⟧) ≫ (shiftFunctor C b).map (sa.hom.app (M, N)) ≫
        (shiftFunctorAdd C a b).inv.app (F.obj (M, N)) := rfl

private def firstSlot {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (r : ℤ)
    (s : tensorShiftFirst C r ⋙ F ≅ F ⋙ shiftFunctor C r) (N : C) :
    shiftFunctor C r ⋙ (Functor.curry.obj F).flip.obj N ≅
      (Functor.curry.obj F).flip.obj N ⋙ shiftFunctor C r :=
  NatIso.ofComponents (fun M ↦ s.app (M, N)) (by
    intro X Y f
    exact s.hom.naturality (X := (X, N)) (Y := (Y, N)) (f, 𝟙 N))

private def secondSlot {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (r : ℤ)
    (s : completedTensorShiftSecond C r ⋙ F ≅ F ⋙ shiftFunctor C r) (M : C) :
    shiftFunctor C r ⋙ (Functor.curry.obj F).obj M ≅
      (Functor.curry.obj F).obj M ⋙ shiftFunctor C r :=
  NatIso.ofComponents (fun N ↦ s.app (M, N)) (by
    intro X Y f
    exact s.hom.naturality (X := (M, X)) (Y := (M, Y)) (𝟙 M, f))

private theorem firstSlot_add {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : tensorShiftFirst C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : tensorShiftFirst C b ⋙ F ≅ F ⋙ shiftFunctor C b) (N : C) :
    firstSlot F (a + b) (firstSlotAdd F a b sa sb) N =
      CommShift.isoAdd (firstSlot F a sa N) (firstSlot F b sb N) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change (firstSlotAdd F a b sa sb).hom.app (M, N) = _
  rw [firstSlotAdd_hom_app, CommShift.isoAdd_hom_app]
  rfl

private theorem secondSlot_add {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C × C ⥤ C) (a b : ℤ)
    (sa : completedTensorShiftSecond C a ⋙ F ≅ F ⋙ shiftFunctor C a)
    (sb : completedTensorShiftSecond C b ⋙ F ≅ F ⋙ shiftFunctor C b) (M : C) :
    secondSlot F (a + b) (secondSlotAdd F a b sa sb) M =
      CommShift.isoAdd (secondSlot F a sa M) (secondSlot F b sb M) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  change (secondSlotAdd F a b sa sb).hom.app (M, N) = _
  rw [secondSlotAdd_hom_app, CommShift.isoAdd_hom_app]
  rfl

attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor tensorShifts
attribute [local instance 3000] integralTowerHasDerivedCategory
set_option backward.defeqAttrib.useBackward true

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The fixed completed-tensor comparisons are coherent in each individual slot.
Source: Stacks 011G, 014E and 0941; the parent proof, Steps 5 and 6.
(blueprint: lem-pur-completed-tensor-prescribed-slot-shift-laws).

Proof: on good flat-term K-flat representatives, the first-slot finite
comparison has coefficient 1 and the second-slot comparison coefficient
(-1)^(ri). Shifts preserve the good-model predicate. Both comparisons
commute with quotient transitions, so they give tower isomorphisms.
Products commute with shifts and preserve the square for 1-s. On the
cone use (b,a) mapped to (b,(-1)^r a), followed by [-1]. The formula is
identity at zero, and successive shifts multiply its second coefficient
to (-1)^(r+s). Thus each slot has the zero/addition equations already on
the good models. The completed model functor inverts resolving
quasi-isomorphisms. Fully faithful restriction through the resolving
localization in each input therefore descends the natural isomorphisms
and their equations uniquely. Their representative squares are exactly
integralLeft_normalized and integralRight_normalized. Uniqueness identifies
the descended comparisons with those in tensorShifts, giving the displayed
CommShift structures and the required component identities. -/
theorem completedTensorSlotShiftLaws (W : Scheme.{u}) :
    ∃ (s₁ : ∀ N : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).flip.obj N).CommShift ℤ)
          (s₂ : ∀ M : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).obj M).CommShift ℤ),
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₁ N) r).app M =
              ((tensorShifts l E).integralLeft W r).app (M, N)) ∧
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₂ M) r).app N =
              ((tensorShifts l E).integralRight W r).app (M, N)) := by
  classical
  let F := integralCompletedTensor l E W
  let sl := fun r ↦ (tensorShifts l E).integralLeft W r
  let sr := fun r ↦ (tensorShifts l E).integralRight W r
  obtain ⟨hL⟩ := good_prod_whisker_fullyFaithful l E W (Integral l E W)
  have hleft (a b : ℤ) : sl (a + b) = firstSlotAdd F a b (sl a) (sl b) := by
    apply Iso.ext
    apply hL.map_injective
    apply NatTrans.ext
    funext X
    change (sl (a + b)).hom.app
      (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) =
        (firstSlotAdd F a b (sl a) (sl b)).hom.app
          (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj)
    rw [firstSlotAdd_hom_app]
    exact (completedTensorShift_add_on_good l E W sl sr
      ((tensorShifts l E).integralLeft_normalized W)
      ((tensorShifts l E).integralRight_normalized W) a b X.1 X.2).1
  have hright (a b : ℤ) : sr (a + b) = secondSlotAdd F a b (sr a) (sr b) := by
    apply Iso.ext
    apply hL.map_injective
    apply NatTrans.ext
    funext X
    change (sr (a + b)).hom.app
      (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) =
        (secondSlotAdd F a b (sr a) (sr b)).hom.app
          (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj)
    rw [secondSlotAdd_hom_app]
    exact (completedTensorShift_add_on_good l E W sl sr
      ((tensorShifts l E).integralLeft_normalized W)
      ((tensorShifts l E).integralRight_normalized W) a b X.1 X.2).2
  have hladd (N : Integral l E W) (a b : ℤ) :
      firstSlot F (a + b) (sl (a + b)) N =
        CommShift.isoAdd (firstSlot F a (sl a) N) (firstSlot F b (sl b) N) := by
    rw [hleft]
    exact firstSlot_add F a b (sl a) (sl b) N
  have hradd (M : Integral l E W) (a b : ℤ) :
      secondSlot F (a + b) (sr (a + b)) M =
        CommShift.isoAdd (secondSlot F a (sr a) M) (secondSlot F b (sr b) M) := by
    rw [hright]
    exact secondSlot_add F a b (sr a) (sr b) M
  let s₁ (N : Integral l E W) : ((Functor.curry.obj F).flip.obj N).CommShift ℤ :=
    { commShiftIso := fun r ↦ firstSlot F r (sl r) N
      commShiftIso_zero := shiftZero_of_add ((Functor.curry.obj F).flip.obj N)
        (fun r ↦ firstSlot F r (sl r) N) (hladd N)
      commShiftIso_add := hladd N }
  let s₂ (M : Integral l E W) : ((Functor.curry.obj F).obj M).CommShift ℤ :=
    { commShiftIso := fun r ↦ secondSlot F r (sr r) M
      commShiftIso_zero := shiftZero_of_add ((Functor.curry.obj F).obj M)
        (fun r ↦ secondSlot F r (sr r) M) (hradd M)
      commShiftIso_add := hradd M }
  exact ⟨s₁, s₂, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

end WeilConjectures.IntegralSystemRealization
