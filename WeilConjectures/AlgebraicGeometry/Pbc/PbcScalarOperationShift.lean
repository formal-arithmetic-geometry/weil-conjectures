/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shift coherence of scalar operation comparisons

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-operation-shift-coherence)
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
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

section ScalarOperationShifts
attribute [local irreducible] completedAdicDerivedChange

private theorem scalarDenseComparison_shift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (G L : B ⥤ E)
    [G.CommShift ℤ] [L.CommShift ℤ] (F : A ⥤ E) [F.CommShift ℤ]
    (α : Q ⋙ L ⟶ F) [NatTrans.CommShift α ℤ] (t : G ⟶ L)
    [NatTrans.CommShift (whiskerLeft Q t ≫ α) ℤ]
    (dense : ∀ Y : B, ∃ (X : A) (_e : Q.obj X ≅ Y), IsIso (α.app X)) :
    NatTrans.CommShift t ℤ := by
  constructor
  intro n
  let s : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    (G.commShiftIso n).hom ≫ whiskerRight t (shiftFunctor E n)
  let u : shiftFunctor B n ⋙ G ⟶ L ⋙ shiftFunctor E n :=
    whiskerLeft (shiftFunctor B n) t ≫ (L.commShiftIso n).hom
  have good (X : A) [IsIso (α.app X)] : s.app (Q.obj X) = u.app (Q.obj X) := by
    apply (cancel_mono ((shiftFunctor E n).mapIso (asIso (α.app X))).hom).1
    change s.app (Q.obj X) ≫ (α.app X)⟦n⟧' =
      u.app (Q.obj X) ≫ (α.app X)⟦n⟧'
    apply (cancel_epi (G.mapIso ((Q.commShiftIso n).app X)).hom).1
    change G.map ((Q.commShiftIso n).hom.app X) ≫ s.app (Q.obj X) ≫
      (α.app X)⟦n⟧' = G.map ((Q.commShiftIso n).hom.app X) ≫ u.app (Q.obj X) ≫
      (α.app X)⟦n⟧'
    have ht := NatTrans.shift_app_comm (whiskerLeft Q t ≫ α) n X
    have ha := NatTrans.shift_app_comm α n X
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.map_comp,
      Functor.commShiftIso_comp_hom_app, Category.assoc] at ht ha
    rw [← ha, ← t.naturality_assoc] at ht
    simpa only [s, u, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using ht
  ext Y
  obtain ⟨X, e, hX⟩ := dense Y
  let := hX
  have h := congrArg (fun f ↦ f ≫ (L ⋙ shiftFunctor E n).map e.hom) (good X)
  rw [← s.naturality, ← u.naturality] at h
  exact (cancel_epi (((shiftFunctor B n) ⋙ G).mapIso e).hom).1 h

private theorem scalarComplexComp_shift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ := by
  infer_instance

private theorem scalarComplexNatIso_shift
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (e : F ≅ G) :
    NatTrans.CommShift (NatIso.mapHomologicalComplex e (.up ℤ)).hom ℤ := by
  change NatTrans.CommShift (NatTrans.mapHomologicalComplex e.hom (.up ℤ)) ℤ
  infer_instance

-- `moduleBinaryBiproducts` has a free universe and leaves a stuck universe constraint here.
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarActualAdjunction_shift
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (pbcActualDerivedAdjunction g d).CommShift ℤ := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have := pbcActualPullUniversal g d
  have : (pbcActualDerivedPull g d).IsRightKanExtension (pbcActualPullCounit g d) :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
  let : NatTrans.CommShift (pbcActualPullCounit g d) ℤ :=
    (pbcActualPullShift_exists g d).exists.choose_spec
  let : NatTrans.CommShift (pbcActualPushUnit g d) ℤ :=
    (pbcActualPushShift_exists g d).exists.choose_spec
  apply Adjunction.CommShift.mk' _ ℤ
  apply CategoryTheory.normalized_unit_commShift DerivedCategory.Qh DerivedCategory.Qh
    ((pbcActualModulePull g d).mapHomotopyCategory (.up ℤ))
    ((pbcActualModulePush g d).mapHomotopyCategory (.up ℤ))
    (pbcActualDerivedPull g d) (pbcActualDerivedPush g d)
    ((pbcActualModuleAdjunction g d).mapHomotopyCategory (.up ℤ))
    (pbcActualDerivedAdjunction g d) (pbcActualPullCounit g d) (pbcActualPushUnit g d)
  intro M
  exact ((pbcActualModuleAdjunction g d).mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (pbcActualPullCounit g d) (pbcActualPushUnit g d) M

private theorem scalarReflectionMap_shift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (C : A ⥤ B) [C.CommShift ℤ] (L : A ⥤ A) [L.CommShift ℤ]
    (M : B ⥤ B) [M.CommShift ℤ]
    (η : 𝟭 A ⟶ L) [NatTrans.CommShift η ℤ]
    (ε : 𝟭 B ⟶ M) [NatTrans.CommShift ε ℤ]
    (κ : C ⋙ M ⟶ L ⋙ C)
    (hn : ∀ K, ε.app (C.obj K) ≫ κ.app K = C.map (η.app K))
    (ext : ∀ (n : ℤ) (K : A)
      (a b : M.obj (C.obj (K⟦n⟧)) ⟶ (C.obj (L.obj K))⟦n⟧),
      ε.app (C.obj (K⟦n⟧)) ≫ a = ε.app (C.obj (K⟦n⟧)) ≫ b → a = b) :
    NatTrans.CommShift κ ℤ := by
  constructor
  intro n
  ext K
  apply ext n K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    commShiftIso_comp_hom_app, Category.assoc]
  have hε (N : B) : ε.app (N⟦n⟧) ≫ (M.commShiftIso n).hom.app N =
      (shiftFunctor B n).map (ε.app N) := by
    simpa only [Functor.comp_obj, Functor.id_obj,
      Functor.commShiftIso_id_hom_app, Category.id_comp] using
      (NatTrans.shift_app_comm ε n N).symm
  have hη : (shiftFunctor A n).map (η.app K) =
      η.app (K⟦n⟧) ≫ (L.commShiftIso n).hom.app K := by
    simpa only [Functor.comp_obj, Functor.id_obj,
      Functor.commShiftIso_id_hom_app, Category.id_comp] using
      NatTrans.shift_app_comm η n K
  have hcn := (C.commShiftIso n).hom.naturality (η.app K)
  have hen := (ε.naturality ((C.commShiftIso n).hom.app K)).symm
  change ε.app (C.obj (K⟦n⟧)) ≫ M.map ((C.commShiftIso n).hom.app K) =
      (C.commShiftIso n).hom.app K ≫ ε.app ((C.obj K)⟦n⟧) at hen
  calc
    _ = (C.commShiftIso n).hom.app K ≫
        (ε.app ((C.obj K)⟦n⟧) ≫ (M.commShiftIso n).hom.app (C.obj K)) ≫
          (shiftFunctor B n).map (κ.app K) := by
      rw [← Category.assoc, hen]
      simp only [Category.assoc]
    _ = (C.commShiftIso n).hom.app K ≫
        (shiftFunctor B n).map (ε.app (C.obj K) ≫ κ.app K) := by
      rw [hε, Functor.map_comp]
    _ = (C.commShiftIso n).hom.app K ≫ (shiftFunctor B n).map (C.map (η.app K)) := by
      rw [hn]
    _ = C.map ((shiftFunctor A n).map (η.app K)) ≫
        (C.commShiftIso n).hom.app (L.obj K) := hcn.symm
    _ = C.map (η.app (K⟦n⟧)) ≫ C.map ((L.commShiftIso n).hom.app K) ≫
        (C.commShiftIso n).hom.app (L.obj K) := by
      rw [hη, Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [← hn]; simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletion_shift (W : Scheme.{u}) :
    NatTrans.CommShift (pbcScalarCompletionIso l E F i W).hom ℤ := by
  let C := pbcEmbeddingAmbientTensor l E F i W
  let L := pbcActualCompletion (pbcIntegralDatum l E) W
  let M := pbcActualCompletion (pbcIntegralDatum l F) W
  let η := pbcActualCompletionUnit (pbcIntegralDatum l E) W
  let ε := pbcActualCompletionUnit (pbcIntegralDatum l F) W
  let κ := pbcScalarCompletionIso l E F i W
  let : NatTrans.CommShift η ℤ :=
    (pbcActualCompletionShift_exists (pbcIntegralDatum l E) W).exists.choose_spec
  let : NatTrans.CommShift ε ℤ :=
    (pbcActualCompletionShift_exists (pbcIntegralDatum l F) W).exists.choose_spec
  apply scalarReflectionMap_shift C L M η ε κ.hom
  · intro K
    dsimp only [κ]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E F i W).exists.choose_spec K
  · intro n K a b hab
    have := pbcComplete_iso W (pbcIntegralDatum l F)
    let e : M.obj (C.obj (K⟦n⟧)) ≅ (C.obj (L.obj K))⟦n⟧ :=
      ((C ⋙ M).commShiftIso n).app K ≪≫
        (shiftFunctor _ n).mapIso (κ.app K)
    have hComplete : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
        ((C.obj (L.obj K))⟦n⟧) :=
      ObjectProperty.prop_of_iso _ e
        (((ObjectProperty.ι (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))).leftAdjoint.obj
          (C.obj (K⟦n⟧))).property)
    exact pbcCompletion_hom_ext W (pbcIntegralDatum l F) _ _ hComplete a b hab

end ScalarOperationShifts

end AmbientOperations
end AlgebraicGeometry.Scheme
