/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitEventualZeroAux
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # Eventual vanishing in filtered etale sheaf colimits

Source: Stacks Project, Sites, Lemma Tag 0738, and Etale Cohomology, Tag 03Q4.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A section on a quasi-compact etale object which vanishes in a filtered sheaf
colimit vanishes at a later stage (Stacks, Tags 0738, 03Q4). -/
theorem etale_section_colimit_eventual_zero
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) :
    ∀ (i : I) (s : (G.obj i).obj.obj (Opposite.op U)),
      ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0 →
      ∃ (j : I) (f : i ⟶ j), ((G.map f).hom.app (Opposite.op U)).hom s = 0 := by
  intro i s hs
  obtain ⟨K, hK, V, q, hlocal, hsep⟩ :=
    etale_section_colimit_finite_zero_cover X Λ U I G c hc i s hs
  let _ : Finite K := hK
  exact etale_section_colimit_eventual_zero_of_finite_cover
    X Λ U I G i s K V q hlocal hsep

end AlgebraicGeometry
