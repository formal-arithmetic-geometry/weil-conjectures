/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Constant sheaves, localization of sites, pullback and equivalences of sites

## Main results

- `CategoryTheory.Sheaf.isConstant_of_constantSheafIso` and
  `CategoryTheory.Sheaf.isConstant_iff_of_constantSheafIso`: a functor `F` of sheaf
  categories equipped with an isomorphism `constantSheaf J A ⋙ F ≅ constantSheaf K A`
  preserves constancy, and reflects it as soon as `F` is fully faithful. All the results
  below are instances of these two.
- `CategoryTheory.GrothendieckTopology.overPullbackConstantSheafIso` and
  `CategoryTheory.Sheaf.isConstant_over`: the constant sheaf functor commutes with
  localization of a site at an object, so the restriction of a constant sheaf to a
  localized site is constant.
- `CategoryTheory.Functor.constantSheafsheafPullbackIso` and
  `CategoryTheory.Sheaf.isConstant_sheafPullback`: the constant sheaf functor commutes with
  the pullback of sheaves along a continuous functor of sites which preserves a terminal
  object, so the pullback of a constant sheaf is constant.
- `CategoryTheory.Equivalence.constantSheafSheafCongrIso`,
  `CategoryTheory.Sheaf.isConstant_sheafCongr_functor` and
  `CategoryTheory.Sheaf.isConstant_sheafCongr_functor_iff`: for an equivalence of sites the
  equivalence of sheaf categories `CategoryTheory.Equivalence.sheafCongr` commutes with the
  constant sheaf functors, so a sheaf is constant if and only if its transport is.

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Over` since neither imports the other, and additionally
`Mathlib.CategoryTheory.Sites.Pullback` for the pullback of sheaves and
`Mathlib.CategoryTheory.Sites.Equivalence` for equivalences of sites.
-/

@[expose] public section

universe v u'

open CategoryTheory Limits Opposite

noncomputable section

namespace CategoryTheory

section General

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {A : Type*} [Category* A]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- A functor of sheaf categories commuting with the constant sheaf functors preserves
constancy. -/
lemma Sheaf.isConstant_of_constantSheafIso {F : Sheaf J A ⥤ Sheaf K A}
    (i : constantSheaf J A ⋙ F ≅ constantSheaf K A) (G : Sheaf J A) [G.IsConstant J] :
    (F.obj G).IsConstant K := by
  obtain ⟨a, ⟨e⟩⟩ := G.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso K (F.mapIso e.symm ≪≫ i.app a)

/-- A fully faithful functor of sheaf categories commuting with the constant sheaf functors
reflects constancy: `F.obj G` is constant if and only if `G` is. -/
lemma Sheaf.isConstant_iff_of_constantSheafIso {F : Sheaf J A ⥤ Sheaf K A} [F.Full]
    [F.Faithful] (i : constantSheaf J A ⋙ F ≅ constantSheaf K A) (G : Sheaf J A) :
    (F.obj G).IsConstant K ↔ G.IsConstant J := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Sheaf.isConstant_of_constantSheafIso i G⟩
  obtain ⟨a, ⟨e⟩⟩ := (F.obj G).mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _ (F.preimageIso (e.symm ≪≫ (i.app a).symm))

end General

section Over

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v} A] (W : C)
  [HasWeakSheafify J A] [HasWeakSheafify (J.over W) A]
  [∀ P : (Over W)ᵒᵖ ⥤ A, (Over.forget W).op.HasPointwiseRightKanExtension P]

/-- The constant sheaf functor commutes with localization of the site at an object:
the restriction of the constant sheaf at `a : A` to `J.over W` is the constant sheaf
at `a`. -/
def GrothendieckTopology.overPullbackConstantSheafIso :
    constantSheaf J A ⋙ J.overPullback A W ≅ constantSheaf (J.over W) A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      ((Over.forget W).pushforwardContinuousSheafificationCompatibility A (J.over W) J).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ (Over.forget W).op)
      (presheafToSheaf (J.over W) A)

variable {J A} in
/-- The restriction of a constant sheaf to the site localized at an object is
constant. -/
lemma Sheaf.isConstant_over (F : Sheaf J A) [F.IsConstant J] :
    (F.over W).IsConstant (J.over W) :=
  Sheaf.isConstant_of_constantSheafIso (J.overPullbackConstantSheafIso A W) F

end Over

section Pullback

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type u') [Category.{v} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

/-- Sections of the pushforward of a sheaf along `G` over an object `X` are sections of
the sheaf over `G.obj X`. -/
def Functor.sheafPushforwardContinuousCompSheafSectionsObjIso (X : Cᵒᵖ) :
    G.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj X ≅
      (sheafSections K A).obj (G.op.obj X) :=
  NatIso.ofComponents (fun F ↦ Iso.refl _)

variable [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The constant sheaf functor commutes with the pullback of sheaves along a continuous
functor of sites which preserves a terminal object: the pullback of the constant sheaf
at `a : A` is the constant sheaf at `a`. -/
def Functor.constantSheafsheafPullbackIso {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  (((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K)).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso A J K (op T))).leftAdjointUniq
    (constantSheafAdj K A hGT)

variable {A J K} in
/-- The pullback of a constant sheaf along a continuous functor of sites which preserves
a terminal object is constant. -/
lemma Sheaf.isConstant_sheafPullback {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) (F : Sheaf J A) [F.IsConstant J] :
    ((G.sheafPullback A J K).obj F).IsConstant K :=
  Sheaf.isConstant_of_constantSheafIso (G.constantSheafsheafPullbackIso A J K hT hGT) F

end Pullback

section Equivalence

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (e : C ≌ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [e.inverse.IsDenseSubsite K J]
  (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The sections of the transport of a sheaf `G` along an equivalence of sites over `Y : D`
are the sections of `G` over `e.inverse.obj Y`. -/
def Equivalence.sheafCongrFunctorCompSheafSectionsObjIso (Y : D) :
    (e.sheafCongr J K A).functor ⋙ (sheafSections K A).obj (Opposite.op Y) ≅
      (sheafSections J A).obj (Opposite.op (e.inverse.obj Y)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The transport of sheaves along an equivalence of sites commutes with the constant sheaf
functors: both `constantSheaf J A ⋙ functor` and `constantSheaf K A` are left adjoint to
global sections over a terminal object. -/
def Equivalence.constantSheafSheafCongrIso {T : C} (hT : IsTerminal T) :
    constantSheaf J A ⋙ (e.sheafCongr J K A).functor ≅ constantSheaf K A :=
  have hT' : IsTerminal (e.functor.obj T) := hT.isTerminalObj e.functor
  (((constantSheafAdj J A hT).comp (e.sheafCongr J K A).toAdjunction).ofNatIsoRight
    (NatIso.ofComponents (F := (e.sheafCongr J K A).inverse ⋙
      (sheafSections J A).obj (Opposite.op T))
      (G := (sheafSections K A).obj (Opposite.op (e.functor.obj T)))
      (fun _ ↦ Iso.refl _) (fun _ ↦ by
        dsimp
        rw [Category.comp_id, Category.id_comp]
        rfl))).leftAdjointUniq (constantSheafAdj K A hT')

variable {J K A}

/-- The transport of a constant sheaf along an equivalence of sites is constant. -/
lemma Sheaf.isConstant_sheafCongr_functor {T : C} (hT : IsTerminal T)
    (G : Sheaf J A) [G.IsConstant J] :
    ((e.sheafCongr J K A).functor.obj G).IsConstant K :=
  Sheaf.isConstant_of_constantSheafIso (e.constantSheafSheafCongrIso J K A hT) G

/-- A sheaf is constant if and only if its transport along an equivalence of sites is. -/
lemma Sheaf.isConstant_sheafCongr_functor_iff {T : C} (hT : IsTerminal T) (G : Sheaf J A) :
    ((e.sheafCongr J K A).functor.obj G).IsConstant K ↔ G.IsConstant J :=
  Sheaf.isConstant_iff_of_constantSheafIso (e.constantSheafSheafCongrIso J K A hT) G

end Equivalence

end CategoryTheory
