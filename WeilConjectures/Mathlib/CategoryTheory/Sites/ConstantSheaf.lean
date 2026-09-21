/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

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

That identification is compatible with the composition of continuous functors
(`CategoryTheory.Functor.constantSheafsheafPullbackIso_comp`), modulo the comparison
`CategoryTheory.Functor.sheafPullbackComp` of the pullback along a composite with the
composite of the pullbacks.

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Over` since neither imports the other, and additionally
`Mathlib.CategoryTheory.Sites.Pullback` for the pullback of sheaves.
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

/-- The composite of the constant sheaf adjunction on `(C, J)` with the adjunction between
the pullback and the pushforward of sheaves along `G`: it exhibits `a ↦ G^{-1} (a_C)` as a
left adjoint of the sections over `G.obj T`, and is the adjunction from which
`CategoryTheory.Functor.constantSheafsheafPullbackIso` is obtained.

```
                 constantSheaf J A            G^{-1}
            A ---------------------> Sheaf J A -------> Sheaf K A
             <--------------------------------------------
                        Γ(G.obj T, -)
```
-/
def Functor.constantSheafsheafPullbackAdjunction {T : C} (hT : IsTerminal T) :
    constantSheaf J A ⋙ G.sheafPullback A J K ⊣ (sheafSections K A).obj (op (G.obj T)) :=
  ((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K)).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso A J K (op T))

/-- The constant sheaf functor commutes with the pullback of sheaves along a continuous
functor of sites which preserves a terminal object: the pullback of the constant sheaf
at `a : A` is the constant sheaf at `a`. -/
def Functor.constantSheafsheafPullbackIso {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  (G.constantSheafsheafPullbackAdjunction A J K hT).leftAdjointUniq (constantSheafAdj K A hGT)

omit [HasWeakSheafify K A] in
/-- The unit of `CategoryTheory.Functor.constantSheafsheafPullbackAdjunction` is the unit of
the constant sheaf adjunction on `(C, J)` followed by the sections of the unit of
`G^{-1} ⊣ G_*`:

```
a --unit--> Γ(T, a_C) --Γ(T, unit)--> Γ(T, G_* G^{-1} a_C) = Γ(G.obj T, G^{-1} a_C)
|                                                                    ^
+----------------------------unit------------------------------------+
```
-/
lemma Functor.constantSheafsheafPullbackAdjunction_unit_app {T : C} (hT : IsTerminal T)
    (a : A) :
    (G.constantSheafsheafPullbackAdjunction A J K hT).unit.app a =
      (constantSheafAdj J A hT).unit.app a ≫ ((sheafSections J A).obj (op T)).map
        ((G.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj a)) := by
  simp only [Functor.constantSheafsheafPullbackAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso, NatIso.ofComponents_hom_app,
    Iso.refl_hom]
  exact Category.comp_id _

/-- `CategoryTheory.Functor.constantSheafsheafPullbackIso` is the unique identification
compatible with the units of the two constant sheaf adjunctions:

```
                              Γ(T, unit)                Γ(G.obj T, iso.hom)
a --unit--> Γ(T, a_C) -------------------> Γ(G.obj T, G^{-1} a_C) ----------> Γ(G.obj T, a_D)
 |                                                                                  ^
 +---------------------------------unit---------------------------------------------+
```
-/
lemma Functor.unit_constantSheafsheafPullbackIso_hom_app {T : C} (hT : IsTerminal T)
    (hGT : IsTerminal (G.obj T)) (a : A) :
    (constantSheafAdj J A hT).unit.app a ≫
        ((sheafSections J A).obj (op T)).map
            ((G.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj a)) ≫
          ((sheafSections K A).obj (op (G.obj T))).map
            ((G.constantSheafsheafPullbackIso A J K hT hGT).hom.app a) =
      (constantSheafAdj K A hGT).unit.app a := by
  have h := NatTrans.congr_app
    ((G.constantSheafsheafPullbackAdjunction A J K hT).unit_leftAdjointUniq_hom
      (constantSheafAdj K A hGT)) a
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    G.constantSheafsheafPullbackAdjunction_unit_app A J K hT a, Category.assoc] at h
  -- not `simpa … using h`: the two sides agree only up to the definitional unfolding of
  -- `constantSheafsheafPullbackIso`, which `exact` bridges but the closing step of `simpa`
  -- does not
  exact h

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

section PullbackComp

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  (F : C ⥤ D) (G : D ⥤ E) (A : Type u') [Category.{v} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify L A]
  [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous A K L).IsRightAdjoint]
  [((F ⋙ G).sheafPushforwardContinuous A J L).IsRightAdjoint]
  {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))
  (hGFT : IsTerminal (G.obj (F.obj T)))

/-- **The identification of the pullback of a constant sheaf is compatible with
composition**: the identification of `(F ⋙ G)^{-1} (a_C)` with `a_E` is the composite of the
identifications for `F` and for `G`, read through
`CategoryTheory.Functor.sheafPullbackComp`.

```
constantSheaf J A ⋙ (F ⋙ G)^{-1} --sheafPullbackComp--> constantSheaf J A ⋙ F^{-1} ⋙ G^{-1}
           |                                                             |
   (F ⋙ G)-iso                                                    G^{-1} (F-iso)
           v                                                             v
   constantSheaf L A  <-------------G-iso--------------  constantSheaf K A ⋙ G^{-1}
```
-/
lemma Functor.constantSheafsheafPullbackIso_comp :
    Functor.whiskerLeft (constantSheaf J A) (F.sheafPullbackComp G A J K L).hom ≫
        Functor.whiskerRight (F.constantSheafsheafPullbackIso A J K hT hFT).hom
            (G.sheafPullback A K L) ≫
          (G.constantSheafsheafPullbackIso A K L hFT hGFT).hom =
      ((F ⋙ G).constantSheafsheafPullbackIso A J L hT hGFT).hom := by
  refine Adjunction.eq_leftAdjointUniq_hom
    ((F ⋙ G).constantSheafsheafPullbackAdjunction A J L hT) (constantSheafAdj L A hGFT)
    _ fun a ↦ ?_
  have hu := (F ⋙ G).constantSheafsheafPullbackAdjunction_unit_app A J L hT a
  have hg : ((sheafSections J A).obj (op T)).map
        (((F ⋙ G).sheafAdjunctionContinuous A J L).unit.app ((constantSheaf J A).obj a)) ≫
      ((sheafSections L A).obj (op (G.obj (F.obj T)))).map
        ((F.sheafPullbackComp G A J K L).hom.app ((constantSheaf J A).obj a)) =
      ((sheafSections J A).obj (op T)).map
          ((F.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj a)) ≫
        ((sheafSections K A).obj (op (F.obj T))).map
          ((G.sheafAdjunctionContinuous A K L).unit.app
            ((F.sheafPullback A J K).obj ((constantSheaf J A).obj a))) := by
    have h1 := congrArg ((sheafSections J A).obj (op T)).map
      (F.unit_sheafPullbackComp_hom_app G A J K L ((constantSheaf J A).obj a))
    simp only [Functor.map_comp] at h1
    exact h1
  have hnat : ((sheafSections K A).obj (op (F.obj T))).map
        ((G.sheafAdjunctionContinuous A K L).unit.app
          ((F.sheafPullback A J K).obj ((constantSheaf J A).obj a))) ≫
      ((sheafSections L A).obj (op (G.obj (F.obj T)))).map
        ((G.sheafPullback A K L).map
          ((F.constantSheafsheafPullbackIso A J K hT hFT).hom.app a)) =
      ((sheafSections K A).obj (op (F.obj T))).map
          ((F.constantSheafsheafPullbackIso A J K hT hFT).hom.app a) ≫
        ((sheafSections K A).obj (op (F.obj T))).map
          ((G.sheafAdjunctionContinuous A K L).unit.app ((constantSheaf K A).obj a)) := by
    have h2 := (G.sheafAdjunctionContinuous A K L).unit.naturality
      ((F.constantSheafsheafPullbackIso A J K hT hFT).hom.app a)
    have h3 := congrArg ((sheafSections K A).obj (op (F.obj T))).map h2.symm
    simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at h3
    exact h3
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Functor.comp_obj]
  rw [hu, Category.assoc, reassoc_of% hg, reassoc_of% hnat,
    ← G.unit_constantSheafsheafPullbackIso_hom_app A K L hFT hGFT a,
    ← F.unit_constantSheafsheafPullbackIso_hom_app A J K hT hFT a]
  simp

/-- The inverse form of `CategoryTheory.Functor.constantSheafsheafPullbackIso_comp`, in which
the identification of `(F ⋙ G)^{-1} (a_C)` with `a_E` is run backwards:

```
a_E --(G-iso)⁻¹--> G^{-1} (a_D) --G^{-1} (F-iso)⁻¹--> G^{-1} F^{-1} (a_C)
    --(sheafPullbackComp)⁻¹--> (F ⋙ G)^{-1} (a_C)
```
-/
lemma Functor.constantSheafsheafPullbackIso_inv_app_comp (a : A) :
    ((F ⋙ G).constantSheafsheafPullbackIso A J L hT hGFT).inv.app a =
      (G.constantSheafsheafPullbackIso A K L hFT hGFT).inv.app a ≫
        (G.sheafPullback A K L).map
            ((F.constantSheafsheafPullbackIso A J K hT hFT).inv.app a) ≫
          (F.sheafPullbackComp G A J K L).inv.app ((constantSheaf J A).obj a) := by
  have h : (F.sheafPullbackComp G A J K L).hom.app ((constantSheaf J A).obj a) ≫
        (G.sheafPullback A K L).map
            ((F.constantSheafsheafPullbackIso A J K hT hFT).hom.app a) ≫
          (G.constantSheafsheafPullbackIso A K L hFT hGFT).hom.app a =
      ((F ⋙ G).constantSheafsheafPullbackIso A J L hT hGFT).hom.app a := by
    have h0 := NatTrans.congr_app
      (F.constantSheafsheafPullbackIso_comp G A J K L hT hFT hGFT) a
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h0
    exact h0
  refine (cancel_epi (((F ⋙ G).constantSheafsheafPullbackIso A J L hT hGFT).hom.app a)).1 ?_
  rw [Iso.hom_inv_id_app, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  simp

end PullbackComp

end CategoryTheory
