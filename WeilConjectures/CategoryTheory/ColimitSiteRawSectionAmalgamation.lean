/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import WeilConjectures.CategoryTheory.ColimitSiteRawSectionMatchingLift

/-! # Raw sections: amalgamation on stage-image covers

Source: Stacks Project, Sites, Tag 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Existence of amalgamations of matching families of sections for the raw colimit site.
Stacks Project, Sites, Tag 0A35. -/
theorem colimit_site_raw_section_exists_amalgamation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X)
    (x : (R.map (V.ι.app j).toFunctor).FamilyOfElements (colimit B))
    (hx : x.Compatible) :
    ∃ s, x.IsAmalgamation s := by
  obtain ⟨t, W, T, hcoverT, e, hT, y, hy, himage⟩ :=
    colimit_site_raw_section_matching_lift J F P hfinite hcover hpullback
      V hobjects harrows Q hVpullback i G θ hθ B β hβ hβmap j X R hR x hx
  let A := (sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  have hA : Presieve.IsSheaf (P t.right).toGrothendieck A.obj :=
    (isSheaf_iff_isSheaf_of_type _ A.obj).mp A.property
  obtain ⟨s, hs, _⟩ := hA.isSheafFor_of_mem_precoverage hcoverT y hy
  let m : A.obj ⟶ (V.ι.app t.right).toFunctor.op ⋙ colimit B :=
    β t ≫ Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  refine ⟨(colimit B).map (eqToHom e.symm).op (m.app (op W) s), ?_⟩
  intro Y f hf
  rw [← hT] at hf
  cases hf with
  | mk p =>
    have hn := NatTrans.naturality_apply m p.val.2.op s
    change m.app (op p.val.1) (A.obj.map p.val.2.op s) =
      (colimit B).map ((V.ι.app t.right).toFunctor.map p.val.2).op
        (m.app (op W) s) at hn
    rw [hs p.val.2 p.property] at hn
    calc
      _ = (colimit B).map ((V.ι.app t.right).toFunctor.map p.val.2).op
          (m.app (op W) s) := by
        simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc,
          eqToHom_trans, eqToHom_refl, Category.comp_id]
      _ = m.app (op p.val.1) (y p.val.2 p.property) := hn.symm
      _ = _ := himage p

end CategoryTheory
