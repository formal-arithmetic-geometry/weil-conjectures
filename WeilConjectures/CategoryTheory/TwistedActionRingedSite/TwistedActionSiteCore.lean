/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.Construction.TwistedActionTopology
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.Construction.TwistedActionCoefficient

/-! # Underlying twisted action site and coefficient sheaf

Every site with a continuous autoequivalence `s` and a ring sheaf with a compatible isomorphism
`a` has an underlying integer-labelled twisted action site with a coefficient sheaf.

## References

Motivated by Stacks Project, Tag 00W0.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

/-- The underlying integer-labelled site and its coefficient sheaf. -/
theorem siteCore [HasPullbacks C] :
    ∃ S : Site J s R a,
      letI := S.category
      S.inclusion.IsCocontinuous J S.topology := by
  let := Construction.category s
  let := Construction.inclusion_continuous s J
  let P := Construction.coefficientPresheaf s J R a
  have hP : Presheaf.IsSheaf (Construction.topology s J) P := by
    apply Construction.ring_isSheaf s J P
    exact (Presheaf.isSheaf_of_iso_iff
      (Construction.coefficientPresheafRestriction s J R a)).mpr R.property
  let S : Site J s R a := {
    category := Construction.category s
    inclusion := Construction.inclusion s
    inclusion_obj X := rfl
    arrows := Construction.arrows s
    powerComp := Construction.powerComp s
    arrows_id := Construction.arrows_id s
    arrows_comp := Construction.arrows_comp s
    arrows_inclusion := Construction.arrows_inclusion s
    topology := Construction.topology s J
    topology_eq := Construction.topology_eq s J
    inclusion_continuous := inferInstance
    coefficient := ⟨P, hP⟩
    coefficientRestriction := {
      hom := ⟨(Construction.coefficientPresheafRestriction s J R a).hom⟩
      inv := ⟨(Construction.coefficientPresheafRestriction s J R a).inv⟩
      hom_inv_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext X
        exact Iso.hom_inv_id_app _ X
      inv_hom_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext X
        exact Iso.inv_hom_id_app _ X }
    coefficient_generator := by
      intro X r
      change P.map _ r = _
      rw [Construction.coefficientPresheaf_generator]
      rfl }
  exact ⟨S, (Construction.topology_criterion s J).1⟩

end CategoryTheory.TwistedActionRingedSite
