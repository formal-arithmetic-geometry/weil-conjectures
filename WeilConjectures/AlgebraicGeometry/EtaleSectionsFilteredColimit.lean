/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Sheaf

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitEventualZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitRepresentative

/-!
# Filtered colimits of sections on quasi-compact quasi-separated etale objects

## References

* Stacks Project, Tags 0738 and 03Q4
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Sections over a quasi-compact quasi-separated scheme in the small etale site commute
with filtered colimits of sheaves of modules. The comparison is the unique map whose
composite with each colimit coprojection is the corresponding cocone map evaluated at `U`
(Stacks, Tags 0738 and 03Q4). -/
theorem etale_sections_filtered_colimit
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (_hc : IsColimit c) :
    let E := (sheafSections X.smallEtaleTopology (ModuleCat.{max v w} Λ)).obj
      (Opposite.op U)
    Function.Bijective ((colimit.desc (G ⋙ E) (E.mapCocone c)).hom) := by
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{max v w} Λ)).obj
    (Opposite.op U)
  let F := G ⋙ E
  have : PreservesColimit F (forget (ModuleCat.{max v w} Λ)) :=
    preservesColimit_of_preserves_colimit_cocone
      (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat.{max v w} Λ)))
  let d := E.mapCocone c
  let ψ := colimit.desc F d
  have hψ (i : I) (s : F.obj i) : ψ.hom ((colimit.ι F i).hom s) =
      (d.ι.app i).hom s := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (colimit.ι_desc d i)) s
  constructor
  · apply (injective_iff_map_eq_zero ψ.hom).2
    intro x hx
    obtain ⟨i, s, hs⟩ := Concrete.colimit_exists_rep F x
    have hz : ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0 := by
      change (d.ι.app i).hom s = 0
      rw [← hψ, hs]
      exact hx
    obtain ⟨j, f, hf⟩ := etale_section_colimit_eventual_zero X Λ U I G c _hc i s hz
    have he : (colimit.ι F i).hom s = (colimit.ι F j).hom ((F.map f).hom s) := by
      exact (LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (colimit.w F f)) s).symm
    rw [← hs, he]
    change (colimit.ι F j).hom (((G.map f).hom.app (Opposite.op U)).hom s) = 0
    rw [hf, map_zero]
  · intro t
    obtain ⟨i, s, hs⟩ := etale_section_colimit_representative X Λ U I G c _hc t
    exact ⟨(colimit.ι F i).hom s, (hψ i s).trans hs⟩

end AlgebraicGeometry
