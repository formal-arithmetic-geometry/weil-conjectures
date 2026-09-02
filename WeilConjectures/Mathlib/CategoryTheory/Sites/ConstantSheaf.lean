/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Constant sheaves, localization of sites and pullback

The constant sheaf functor commutes with localization of a site at an object
(`CategoryTheory.GrothendieckTopology.overPullbackConstantSheafIso`); in particular the
restriction of a constant sheaf to a localized site is constant
(`CategoryTheory.Sheaf.isConstant_over`).

More generally, the constant sheaf functor commutes with the pullback of sheaves along
a continuous functor of sites which preserves a terminal object
(`CategoryTheory.Functor.sheafPullbackCommuteConstant`); in particular the pullback of a
constant sheaf is constant (`CategoryTheory.Sheaf.isConstant_sheafPullback`).

Finally, `CategoryTheory.Sheaf.isConstant_sheafEquiv_inverse_iff` is a variant of
mathlib's `CategoryTheory.Sheaf.isConstant_iff_of_equivalence` assuming directly that the
pushforward of sheaves along a dense subsite is an equivalence, rather than the existence
of the limits needed to prove it; this is what makes it applicable to the (large) small
étale site. It specializes to an equivalence of sites in
`CategoryTheory.Sheaf.isConstant_sheafCongr_functor_iff`.

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
    (F.over W).IsConstant (J.over W) := by
  obtain ⟨a, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((J.overPullback A W).mapIso e.symm ≪≫ (J.overPullbackConstantSheafIso A W).app a)

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
    ((G.sheafPullback A J K).obj F).IsConstant K := by
  obtain ⟨a, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((G.sheafPullback A J K).mapIso e.symm ≪≫
      (G.constantSheafsheafPullbackIso A J K hT hGT).app a)

end Pullback

section DenseSubsite

open Functor.IsDenseSubsite

variable {C : Type*} [Category* C] {C' : Type*} [Category* C'] (J : GrothendieckTopology C)
  (K : GrothendieckTopology C') (G : C ⥤ C') [G.IsDenseSubsite J K]
  (A : Type u') [Category.{v} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence]

/-- The constant sheaf functor commutes with the equivalence of sheaf categories induced by
a dense subsite:

```
                constantSheaf J A
         A ────────────────────────→ Sheaf J A
          \                              │
           \ constantSheaf K A            │ (sheafEquiv J K G A).functor
            ↘                             ↓
                                     Sheaf K A
```

This is `CategoryTheory.equivCommuteConstant` with the hypothesis that the pushforward of
sheaves is an equivalence in place of the stronger existence of the limits indexed by the
structured arrow categories of `G.op`, which is unavailable for the (large) small étale
site. -/
def constantSheafSheafEquivIso {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T)) :
    constantSheaf J A ⋙ (sheafEquiv J K G A).functor ≅ constantSheaf K A :=
  ((constantSheafAdj J A hT).comp (sheafEquiv J K G A).toAdjunction).leftAdjointUniq
    (constantSheafAdj K A hT')

/-- The inverse form of `CategoryTheory.constantSheafSheafEquivIso`. -/
def constantSheafSheafEquivIso' {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T)) :
    constantSheaf J A ≅ constantSheaf K A ⋙ (sheafEquiv J K G A).inverse :=
  Functor.isoWhiskerLeft (constantSheaf J A) (sheafEquiv J K G A).unitIso ≪≫
    Functor.isoWhiskerRight (constantSheafSheafEquivIso J K G A hT hT')
      (sheafEquiv J K G A).inverse

variable {J K A} in
/-- A sheaf on a dense subsite is constant if and only if the corresponding sheaf on the
ambient site is. This is `CategoryTheory.Sheaf.isConstant_iff_of_equivalence` with the
weaker hypothesis of `CategoryTheory.constantSheafSheafEquivIso`. -/
lemma Sheaf.isConstant_sheafEquiv_inverse_iff {T : C} (hT : IsTerminal T)
    (hT' : IsTerminal (G.obj T)) (F : Sheaf K A) :
    ((sheafEquiv J K G A).inverse.obj F).IsConstant J ↔ F.IsConstant K :=
  ⟨fun ⟨Y, ⟨i⟩⟩ ↦ ⟨Y, ⟨(constantSheafSheafEquivIso J K G A hT hT').symm.app Y ≪≫
      (sheafEquiv J K G A).functor.mapIso i ≪≫ (sheafEquiv J K G A).counitIso.app F⟩⟩,
    fun ⟨Y, ⟨i⟩⟩ ↦ ⟨Y, ⟨(constantSheafSheafEquivIso' J K G A hT hT').app Y ≪≫
      (sheafEquiv J K G A).inverse.mapIso i⟩⟩⟩

end DenseSubsite

section Equivalence

open Functor.IsDenseSubsite

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (e : C ≌ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [e.inverse.IsDenseSubsite K J]
  (A : Type u') [Category.{v} A] [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The transport of sheaves along an equivalence of sites is the pushforward of sheaves
along the inverse equivalence, hence an equivalence. -/
instance Equivalence.isEquivalence_sheafPushforwardContinuous_inverse :
    (e.inverse.sheafPushforwardContinuous A K J).IsEquivalence :=
  inferInstanceAs ((e.sheafCongr J K A).functor.IsEquivalence)

variable {J K A} in
/-- A sheaf is constant if and only if its transport along an equivalence of sites is. -/
lemma Sheaf.isConstant_sheafCongr_functor_iff {T : D} (hT : IsTerminal T) (F : Sheaf J A) :
    ((e.sheafCongr J K A).functor.obj F).IsConstant K ↔ F.IsConstant J :=
  Sheaf.isConstant_sheafEquiv_inverse_iff (J := K) (K := J) (G := e.inverse) hT
    (hT.isTerminalObj e.inverse) F

end Equivalence

end CategoryTheory
