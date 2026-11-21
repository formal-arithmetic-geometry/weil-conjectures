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
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.ColimitSiteFiniteUnitZeroDetection

/-! # Eventual equality of abelian inverse-image sections

Source: Stacks Project, Sites, Tag 0A35, and Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A unit-characterized comparison has the kernel of the second adjunction unit. -/
private theorem comparison_kernel_iff
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u})
    (a : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
        ((sheafPullback h AddCommGrpCat.{u} T R).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
        (op X))) (Y : D)
    (x y : ((sheafPullback f AddCommGrpCat.{u} T S).obj G).obj.obj (op Y)) :
    a.hom.app (op Y) x = a.hom.app (op Y) y ↔
      ((sheafAdjunctionContinuous g AddCommGrpCat.{u} S R).unit.app
        ((sheafPullback f AddCommGrpCat.{u} T S).obj G)).hom.app (op Y) x =
      ((sheafAdjunctionContinuous g AddCommGrpCat.{u} S R).unit.app
        ((sheafPullback f AddCommGrpCat.{u} T S).obj G)).hom.app (op Y) y := by
  subst h
  let L := sheafPullback f AddCommGrpCat.{u} T S
  let Rf := f.sheafPushforwardContinuous AddCommGrpCat.{u} T S
  let Rg := g.sheafPushforwardContinuous AddCommGrpCat.{u} S R
  let A := sheafAdjunctionContinuous f AddCommGrpCat.{u} T S
  let B := sheafAdjunctionContinuous g AddCommGrpCat.{u} S R
  let H := sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R
  let e := (A.comp B).leftAdjointUniq H
  let b := B.unit.app (L.obj G) ≫ Rg.map (e.hom.app G)
  have hab : a = b := by
    apply (A.homEquiv G _).injective
    rw [A.homEquiv_unit]
    have he := (A.comp B).unit_leftAdjointUniq_hom_app H G
    rw [A.comp_unit_app B G] at he
    change A.unit.app G ≫ Rf.map (B.unit.app (L.obj G)) ≫
      Rf.map (Rg.map (e.hom.app G)) = H.unit.app G at he
    rw [← Rf.map_comp] at he
    change A.unit.app G ≫ Rf.map a = A.unit.app G ≫ Rf.map b
    rw [he]
    ext1
    apply NatTrans.ext
    funext X
    exact (Arrow.mk_inj _ _).mp (ha (unop X))
  rw [hab]
  change (e.hom.app G).hom.app (op (g.obj Y))
      ((B.unit.app (L.obj G)).hom.app (op Y) x) =
    (e.hom.app G).hom.app (op (g.obj Y))
      ((B.unit.app (L.obj G)).hom.app (op Y) y) ↔ _
  exact (ConcreteCategory.bijective_of_isIso
    ((e.hom.app G).hom.app (op (g.obj Y)))).1.eq_iff

/-- Source: Stacks Project, Sites, Tag 0A35, presentation independence and
unit-compatible adjunction identification; abelian extension by Modules on Sites,
Tag 03CO. -/
theorem colimit_site_abelian_section_eventual_equality
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
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i) (t : Under i)
    (x y : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
        (op ((F.map t.hom).toFunctor.obj U)))
    (hxy : (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) x =
      (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) x =
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) y := by
  let H := (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let W := (F.map t.hom).toFunctor.obj U
  have hv := comparison_kernel_iff (P i).toGrothendieck (P t.right).toGrothendieck
    Q.toGrothendieck (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor
    (V.ι.app i).toFunctor (congrArg Cat.Hom.toFunctor (V.w t.hom))
    G (α t) (hα t) W x y
  have hz : ((sheafAdjunctionContinuous (V.ι.app t.right).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op W)
        (x - y) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hv.mp hxy
  obtain ⟨k, d, hd⟩ := colimit_site_finite_unit_zero_detection
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
    t.right H W (x - y) hz
  let t' : Under i := Under.mk (t.hom ≫ d)
  let b : t ⟶ t' := Under.homMk d
  refine ⟨t', b, ?_⟩
  apply (comparison_kernel_iff (P i).toGrothendieck (P t.right).toGrothendieck
    (P t'.right).toGrothendieck (F.map t.hom).toFunctor (F.map b.right).toFunctor
    (F.map t'.hom).toFunctor (by
      change (F.map t.hom ≫ F.map b.right).toFunctor = _
      rw [← F.map_comp, Under.w b]) G (θ t t' b) (hθ t t' b) W x y).mpr
  change ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
    (P t.right).toGrothendieck (P k).toGrothendieck).unit.app H).hom.app (op W) x =
    ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck (P k).toGrothendieck).unit.app H).hom.app (op W) y
  simpa only [map_sub, sub_eq_zero] using hd

end CategoryTheory
