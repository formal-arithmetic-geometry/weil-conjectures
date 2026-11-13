/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Finite
import WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
/-! Source: Stacks Project, Sites Tag 0738(4). -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Sections on an affine étale object preserve filtered colimits of sheaves for the
finite affine étale pretopology (Stacks, Tags 0738, 00VM and 002W). -/
theorem affineSections_colimit
    {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (E : J ⥤ Sheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1)))
    (K : Cocone E) (hK : IsColimit K) (W : S.FullAffineEtale) :
    Nonempty (IsColimit (((sheafSections (Scheme.fullAffineEtaleTopology S)
      (Type (u + 1))).obj (op W)).mapCocone K))  := by
  obtain ⟨P, hP⟩ := Scheme.fullAffineEtalePrecoverage_isPretopology S
  have hfinite : Scheme.fullAffineEtalePrecoverage S ≤ Precoverage.finite S.FullAffineEtale := by
    intro X R hR
    obtain ⟨n, V, f, rfl, _, _⟩ := hR
    exact Precoverage.ofArrows_mem_finite V f
  have : CreatesColimit E
      (sheafToPresheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1))) :=
    Sheaf.createsColimitOfIsSheaf E (fun e he ↦ by
      rw [isSheaf_iff_isSheaf_of_type]
      change Presieve.IsSheaf (Scheme.fullAffineEtalePrecoverage S).toGrothendieck e.pt
      have hcov : P.toCoverage.toPrecoverage = Scheme.fullAffineEtalePrecoverage S := hP
      have ht : P.toCoverage.toGrothendieck =
          (Scheme.fullAffineEtalePrecoverage S).toGrothendieck :=
        (Coverage.toGrothendieck_toPrecoverage P.toCoverage).symm.trans
          (congrArg Precoverage.toGrothendieck hcov)
      exact ht ▸ ((Presieve.isSheaf_coverage P.toCoverage e.pt).mpr (by
        intro X R hR
        have hf : R.uncurry.Finite := hfinite X (by simpa [hP] using hR)
        exact CategoryTheory.finitePresieve_isSheafFor_filteredColimit _ e he R hf
          (fun i ↦ Presieve.IsSheaf.isSheafFor_of_mem_precoverage
            ((isSheaf_iff_isSheaf_of_type _ _).mp (E.obj i).property)
            (by simpa [hP] using hR)))))
  let F := (sheafSections (Scheme.fullAffineEtaleTopology S) (Type (u + 1))).obj (op W)
  have : PreservesColimit E F := by
    change PreservesColimit E
      (sheafToPresheaf (Scheme.fullAffineEtaleTopology S) (Type (u + 1)) ⋙
        (evaluation _ _).obj (op W))
    infer_instance
  exact ⟨isColimitOfPreserves F hK⟩
end AlgebraicGeometry
