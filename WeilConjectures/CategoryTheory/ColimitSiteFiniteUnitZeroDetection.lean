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
import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.ColimitSiteFiniteSectionColimitPresentation
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Zero detection for source sections with finite covering axioms

Source: Stacks Project, Sites, Tag 0A35, the section formula and its adjunction
paragraph; Modules on Sites, Tag 03CO, abelian extension.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, equation-compute-pullback-to-limit
and the presentation, sheaf-condition and adjunction paragraphs; abelian extension
by Modules on Sites, Tag 03CO. -/
theorem colimit_site_finite_unit_zero_detection
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
    (j : J) (H : Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (X : F.obj j) (z : H.obj.obj (op X))
    (hz : ((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
      (P j).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op X) z = 0) :
    ∃ (k : J) (d : j ⟶ k),
      ((sheafAdjunctionContinuous (F.map d).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck (P k).toGrothendieck).unit.app H).hom.app (op X) z = 0 := by
  obtain ⟨D, e, c, β, α, ⟨hc⟩, hstage, hlimit⟩ :=
    colimit_site_finite_section_colimit_presentation
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback j H X
  let i : Under j := Under.mk (𝟙 j)
  have hrep : c.ι.app i (e.app i z) = c.ι.app i 0 := by
    apply ((ConcreteCategory.isIso_iff_bijective β.hom).mp inferInstance).1
    have hu := ConcreteCategory.congr_hom (hlimit i) z
    change β.hom (c.ι.app i (e.app i z)) = _ at hu
    rw [map_zero, map_zero]
    exact hu.trans hz
  obtain ⟨a, f, hf⟩ := (hc.eq_iff' (e.app i z) 0).mp hrep
  have hn := ConcreteCategory.congr_hom (e.naturality f) z
  have he : e.app a z = 0 := by
    change e.app a z = D.map f (e.app i z) at hn
    rw [map_zero] at hf
    exact hn.trans hf
  refine ⟨a.right, a.hom, ?_⟩
  have hu := ConcreteCategory.congr_hom (hstage a) z
  change (α a).hom (e.app a z) = _ at hu
  rw [he, map_zero] at hu
  exact hu.symm

end CategoryTheory
