/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits

import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit

/-!
# Sections of filtered colimits on sites with finite coverings

## References

* Stacks Project, Sites, Lemma 0738(4), and Modules on Sites, Lemma 03CO.
-/

@[expose] public section

universe u

open CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem isSheaf_filteredColimit_types
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Cᵒᵖ ⥤ Type u) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i, Presheaf.IsSheaf J.toGrothendieck (D.obj i)) :
    Presheaf.IsSheaf J.toGrothendieck c.pt := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro X R hR
  have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
  exact finitePresieve_isSheafFor_filteredColimit D c hc R (hfinite X hR)
    (fun i ↦ ((isSheaf_iff_isSheaf_of_type _ _).mp (hD i)).isSheafFor_of_mem_precoverage hR)

/-- On a site with finite covering presieves, the canonical map from the filtered
colimit of sections to the sections of a given sheaf colimit is bijective.
Source: Stacks Project, Sites, Lemma 0738(4). -/
/- The sectionwise map admits a two-sided inverse. -/
theorem siteFilteredColimit_sections_inverse
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Sheaf J.toGrothendieck (Type u))
    (c : Cocone D) (hc : IsColimit c) (U : C) :
    ∃ g, Function.LeftInverse g
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck (Type u)).obj (op U))
        (((sheafSections J.toGrothendieck (Type u)).obj (op U)).mapCocone c)) ∧
      Function.RightInverse g
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck (Type u)).obj (op U))
        (((sheafSections J.toGrothendieck (Type u)).obj (op U)).mapCocone c)) := by
  classical
  have : CreatesColimit D (sheafToPresheaf J.toGrothendieck (Type u)) :=
    Sheaf.createsColimitOfIsSheaf D (fun e he ↦
      isSheaf_filteredColimit_types J hfinite _ e he (fun i ↦ (D.obj i).property))
  have : PreservesColimit D
      ((sheafSections J.toGrothendieck (Type u)).obj (op U)) := by
    change PreservesColimit D
      (sheafToPresheaf J.toGrothendieck (Type u) ⋙ (evaluation _ _).obj (op U))
    infer_instance
  let F := (sheafSections J.toGrothendieck (Type u)).obj (op U)
  have h := isColimitOfPreserves F hc
  have hi : IsIso (colimit.desc (D ⋙ F) (F.mapCocone c)) :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp ⟨h⟩
  let e := asIso (colimit.desc (D ⋙ F) (F.mapCocone c))
  exact ⟨e.inv, fun x ↦ e.hom_inv_id_apply x, fun x ↦ e.inv_hom_id_apply x⟩

/-- On a site with finite covering presieves, the canonical map from the filtered colimit of
sections to the sections of a given sheaf colimit of set-valued sheaves is bijective. -/
theorem siteFilteredColimit_sections_bijective
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Sheaf J.toGrothendieck (Type u))
    (c : Cocone D) (hc : IsColimit c) (U : C) :
    Function.Bijective
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck (Type u)).obj (op U))
        (((sheafSections J.toGrothendieck (Type u)).obj (op U)).mapCocone c)) := by
  apply Function.bijective_iff_has_inverse.mpr
  obtain ⟨g, hg₁, hg₂⟩ := siteFilteredColimit_sections_inverse J hfinite D c hc U
  exact ⟨g, hg₁, hg₂⟩

/-- For abelian sheaves on a site with finite coverings, the canonical map from the
filtered colimit of section groups to the sections of a given sheaf colimit is an isomorphism.
Source: Stacks Project, Sites, Lemma 0738(4), and Modules on Sites, Lemma 03CO. -/
theorem siteFilteredColimit_sections_isIso
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (hfinite : J ≤ Precoverage.finite C)
    {Λ : Type u} [SmallCategory Λ] [IsFiltered Λ]
    (D : Λ ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (c : Cocone D) (hc : IsColimit c) (U : C) :
    IsIso
      (colimit.desc (D ⋙ (sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U))
        (((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U)).mapCocone c)) := by
  have : CreatesColimit D (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}) := by
    apply Sheaf.createsColimitOfIsSheaf
    intro e he
    rw [Presheaf.isSheaf_iff_isSheaf_comp J.toGrothendieck e.pt
      (forget AddCommGrpCat.{u})]
    let F := (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type u)).obj (forget AddCommGrpCat)
    exact isSheaf_filteredColimit_types J hfinite _ (F.mapCocone e)
      (isColimitOfPreserves F he) (fun i ↦
        (Presheaf.isSheaf_iff_isSheaf_comp J.toGrothendieck (D.obj i).obj
          (forget AddCommGrpCat.{u})).mp
          (D.obj i).property)
  have : PreservesColimit D
      ((sheafSections J.toGrothendieck AddCommGrpCat.{u}).obj (op U)) := by
    change PreservesColimit D
      (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op U))
    infer_instance
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.mp
    ⟨isColimitOfPreserves _ hc⟩

end CategoryTheory
