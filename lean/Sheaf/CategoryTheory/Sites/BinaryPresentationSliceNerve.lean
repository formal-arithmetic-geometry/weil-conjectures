/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.CategoryTheory.Sites.BinaryPresentationModuleData
import all Sheaf.CategoryTheory.SheafSubcategoryComparison
import all Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable

/-! # The slice nerve of a specified subcanonical presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private def localizedEquivalence {E : Type u} [SmallCategory E]
    (K : GrothendieckTopology E) (Z : E) :
    Sheaf (K.over Z) (Type u) ≌
      Over ((presheafToSheaf K (Type u)).obj (yoneda.obj Z)) := by
  have : IsIso (unitTransformation K Z) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact unitComparison_isIso K Z
  have : IsIso (counitTransformation K Z) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact counitComparison_isIso K Z
  exact Equivalence.mk (extensionFunctor K Z) (fibreFunctor K Z)
    (asIso (unitTransformation K Z)) (asIso (counitTransformation K Z))

section
variable {C E : Type u} [SmallCategory C] [SmallCategory E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology E} [K.Subcanonical]
  (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
  (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
  (hN : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F)
  (Z : E)

private def representedIso :
    N.functor.obj (F.obj Z) ≅ (presheafToSheaf K (Type u)).obj (yoneda.obj Z) :=
  (fullyFaithfulSheafToPresheaf K (Type u)).preimageIso
    (hN.app (F.obj Z) ≪≫ (nerve_representable_iso F).app Z ≪≫
      isoSheafify K (K.yoneda.obj Z).property)

private def sliceEquivalenceNerve : Over (F.obj Z) ≌ Sheaf (K.over Z) (Type u) :=
  (Over.post N.functor).asEquivalence.trans
    ((Over.mapIso (representedIso F N hN Z)).trans (localizedEquivalence K Z).symm)

private theorem fibre_condition (B : Over (F.obj Z)) (A : Over Z)
    (s : (N.functor.obj B.left).obj.obj (op A.left)) :
    ((representedIso F N hN Z).hom.hom.app (op A.left)
        ((N.functor.map B.hom).hom.app (op A.left) s) =
      (toSheafify K (yoneda.obj Z)).app (op A.left) A.hom) ↔
    (hN.hom.app B.left).app (op A.left) s ≫ B.hom = F.map A.hom := by
  let η := toSheafify K (yoneda.obj Z)
  have hη : IsIso η := isIso_toSheafify K (K.yoneda.obj Z).property
  have hηinj : Function.Injective (η.app (op A.left)) := injective_of_mono _
  change η.app (op A.left)
      (F.preimage ((hN.hom.app (F.obj Z)).app (op A.left)
        ((N.functor.map B.hom).hom.app (op A.left) s))) =
      η.app (op A.left) A.hom ↔ _
  rw [hηinj.eq_iff]
  have hn := congrArg (fun a ↦ a.app (op A.left) s) (hN.hom.naturality B.hom)
  change (hN.hom.app (F.obj Z)).app (op A.left)
      ((N.functor.map B.hom).hom.app (op A.left) s) =
    (hN.hom.app B.left).app (op A.left) s ≫ B.hom at hn
  rw [hn]
  constructor
  · intro h
    simpa using congrArg F.map h
  · intro h
    apply F.map_injective
    simpa using h

private def sliceSectionEquiv (B : Over (F.obj Z)) (A : Over Z) :
    ((sliceEquivalenceNerve F N hN Z).functor.obj B).obj.obj (op A) ≃
      ((Over.post F).obj A ⟶ B) where
  toFun s := Over.homMk ((hN.hom.app B.left).app (op A.left) s.val)
    ((fibre_condition F N hN Z B A s.val).mp s.property)
  invFun f := ⟨(hN.inv.app B.left).app (op A.left) f.left, by
    apply (fibre_condition F N hN Z B A _).mpr
    have hh := ConcreteCategory.congr_hom
      ((hN.app B.left).inv_hom_id_app (op A.left)) f.left
    exact (congrArg (fun t ↦ t ≫ B.hom) hh).trans (Over.w f)⟩
  left_inv s := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((hN.app B.left).hom_inv_id_app (op A.left)) s.val
  right_inv f := by
    apply Over.OverMorphism.ext
    exact ConcreteCategory.congr_hom
      ((hN.app B.left).inv_hom_id_app (op A.left)) f.left

private def sliceNerveIso :
    (sliceEquivalenceNerve F N hN Z).functor ⋙ sheafToPresheaf (K.over Z) (Type u) ≅
      yoneda ⋙ (Functor.whiskeringLeft (Over Z)ᵒᵖ
        (Over (F.obj Z))ᵒᵖ (Type u)).obj (Over.post F).op := by
  refine NatIso.ofComponents (fun B ↦ NatIso.ofComponents
    (fun A ↦ (sliceSectionEquiv F N hN Z B A.unop).toIso) ?_) ?_
  · intro A A' f
    ext s
    apply Over.OverMorphism.ext
    exact ConcreteCategory.congr_hom
      ((hN.hom.app B.left).naturality f.unop.left.op) s.val
  · intro B B' f
    ext A s
    apply Over.OverMorphism.ext
    exact congrArg (fun a ↦ a.app (op A.unop.left) s.val)
      (hN.hom.naturality f.left)

end

/-- The nerve equivalence restricts to the actual localized topology over each site object.
Source: Stacks Sites 00Y1 and 04GZ (blueprint: lem-sp-nerve-slice-equivalence).
Proof: pass to over categories under N, identify N(F Z) with the sheafified representable
using the nerve formula and full faithfulness of F, and apply the localized fibre
 equivalence. Its sections are exactly the arrows over F Z, naturally in both variables. -/
theorem exists_binaryPresentationSliceNerve
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E} [K.Subcanonical]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (hN : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F) (Z : E) :
    ∃ e : Over (F.obj Z) ≌ Sheaf (K.over Z) (Type u),
      Nonempty (e.functor ⋙ sheafToPresheaf (K.over Z) (Type u) ≅
        yoneda ⋙ (Functor.whiskeringLeft (Over Z)ᵒᵖ
          (Over (F.obj Z))ᵒᵖ (Type u)).obj (Over.post F).op) := by
  exact ⟨sliceEquivalenceNerve F N hN Z, ⟨sliceNerveIso F N hN Z⟩⟩

end CategoryTheory
