/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import WeilConjectures.CategoryTheory.ColimitSiteCoveringConstructionParts
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-! # A step in the filtered colimit site construction.

Source: Stacks Project, Sites, Tags 09YL and 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 09YL, and the first
paragraph of Tag 0A35. -/
theorem colimit_site_covering_construction
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
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        ∃ (_ : Q.HasIsos) (_ : Q.IsStableUnderFiniteComposition)
          (_ : Q.IsStableUnderFiniteBaseChange) (_ : Q.HasPullbacks),
          (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor) ∧
          Nonempty (∀ j : J, (V.ι.app j).toFunctor.IsContinuous
            (P j).toGrothendieck Q.toGrothendieck) := by
  obtain ⟨hisos, hcomp, hbase, hpb, _⟩ :=
    colimit_site_covering_axioms J F P hfinite hcover hpullback V hobjects harrows Q hQ
  obtain ⟨hpres, hcontinuous⟩ :=
    colimit_site_covering_continuity J F P hfinite hcover hpullback V hobjects harrows Q hQ
  exact ⟨hisos, hcomp, hbase, hpb, hpres, hcontinuous⟩

end CategoryTheory
