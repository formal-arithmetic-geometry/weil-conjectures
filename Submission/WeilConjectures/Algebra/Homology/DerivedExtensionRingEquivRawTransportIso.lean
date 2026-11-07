/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Equivalence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Transport of derived scalar extension through ring equivalences -/

@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Precomposition with a functor `P` along which whiskering is fully faithful preserves right
Kan extensions. -/
theorem kan_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    [((Functor.whiskeringLeft A C H).obj P).Full]
    [((Functor.whiskeringLeft A C H).obj P).Faithful]
    (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    L.IsRightKanExtension ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α) := by
  classical
  let W := (Functor.whiskeringLeft A C H).obj P
  let β := (Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α
  let lift (s : Functor.RightExtension (P ⋙ Q) (P ⋙ F)) : s.left ⟶ L :=
    L.liftOfIsRightKanExtension α s.left
      (W.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
  have fac (s : Functor.RightExtension (P ⋙ Q) (P ⋙ F)) :
      Functor.whiskerLeft (P ⋙ Q) (lift s) ≫ β = s.hom := by
    have hf := L.liftOfIsRightKanExtension_fac α s.left
      (W.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
    have hh := congrArg (fun f ↦ W.map f) hf
    simp only [Functor.map_comp, Functor.map_preimage] at hh
    ext X
    have hX := congr_app hh X
    simpa [lift, β, W] using hX
  refine ⟨⟨CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  intro s m
  apply CostructuredArrow.hom_ext
  apply L.hom_ext_of_isRightKanExtension α
  apply W.map_injective
  have hm := m.w
  have hf := fac s
  ext X
  have hmX := congr_app hm X
  have hfX := congr_app hf X
  dsimp at hmX
  dsimp [β] at hfX
  simp only [Category.comp_id, Category.id_comp] at hmX hfX
  simpa [β, W, Category.id_comp] using hmX.trans hfX.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_postcomp_equivalence
    {C D H H' : Type*} [Category C] [Category D] [Category H] [Category H']
    (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H) (E : H ⥤ H') [E.IsEquivalence]
    (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    (L ⋙ E).IsRightKanExtension
      ((Functor.associator Q L E).inv ≫ Functor.whiskerRight α E) := by
  classical
  let T := Functor.RightExtension.postcompose₂ Q F E
  have : T.IsEquivalence := by
    let i : (Functor.whiskeringRight D H H').obj E ⋙
        (Functor.whiskeringLeft C D H').obj Q ≅
      (Functor.whiskeringLeft C D H).obj Q ⋙
        (Functor.whiskeringRight C H H').obj E :=
      NatIso.ofComponents (fun X ↦ (Functor.associator Q X E).symm) (by
        intro X Y f
        ext x
        simp)
    change (CostructuredArrow.map₂ i.hom (𝟙 (F ⋙ E))).IsEquivalence
    let _ : IsIso (𝟙 (F ⋙ E)) := inferInstance
    apply CostructuredArrow.isEquivalenceMap₂
  exact ⟨⟨CategoryTheory.Limits.IsTerminal.ofIso
    ((CategoryTheory.Limits.IsTerminal.isTerminalIffObj T _).toFun
      (L.isUniversalOfIsRightKanExtension α))
    (Functor.RightExtension.postcompose₂ObjMkIso E α)⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F) [L.IsRightKanExtension α] :
    ∃ β : Q' ⋙ L ⟶ F', L.IsRightKanExtension β := by
  classical
  let T := ((Functor.rightExtensionEquivalenceOfIso₁ i F).trans
    (Functor.rightExtensionEquivalenceOfIso₂ Q' j)).functor
  refine ⟨(T.obj (Functor.RightExtension.mk L α)).hom, ⟨⟨?_⟩⟩⟩
  exact (CategoryTheory.Limits.IsTerminal.isTerminalIffObj T _).toFun
    (L.isUniversalOfIsRightKanExtension α)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complex_universal
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    ∃ α : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      L.IsRightKanExtension α := by
  let := h
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
    (HomotopyCategory.quasiIso _ (.up ℤ))
  let P := HomotopyCategory.quotient C (.up ℤ)
  let α := (Functor.associator P DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft P ε
  let := kan_precomp_full P DerivedCategory.Qh _ L ε
  let j : P ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  exact kan_change_iso L (DerivedCategory.quotientCompQhIso C) j α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    (e : C ≌ D) [e.functor.Additive] : e.functor.mapDerivedCategory.IsEquivalence := by
  let ec := e.mapHomologicalComplex (.up ℤ)
  let F := e.functor.mapHomologicalComplex (.up ℤ)
  let G := e.inverse.mapHomologicalComplex (.up ℤ)
  let α : (F ⋙ DerivedCategory.Q) ⋙ e.inverse.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.unitIso.symm DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  let β : (G ⋙ DerivedCategory.Q) ⋙ e.functor.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor _
  exact Localization.isEquivalence
    (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (.up ℤ))
    (F ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory
    (G ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory α β

end ModuleCat
