/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsDescentEquality
import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsDescentSections

/-! # Degree-zero continuity for the specified inverse image

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Degree-zero continuity compares stalk sections with the inverse image specified
by its adjunction to direct image, rather than with an arbitrary functor. -/
theorem strictHenselian_stalkSections_comparison_iso
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology) :
    Nonempty (etaleObjectStalkSections X i x ≅
      H ⋙ (sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 _)))) := by
  let c := LocalStalkSections.comparison i hi_inclusion x H hH
  have hc (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : IsIso (c.app F) := by
    apply (ConcreteCategory.isIso_iff_bijective (c.app F)).2
    constructor
    · intro a b hab
      obtain ⟨U, s, rfl⟩ :=
        Concrete.colimit_exists_rep (LocalStalkSections.neighbourhoodDiagram i x F) a
      obtain ⟨V, t, rfl⟩ :=
        Concrete.colimit_exists_rep (LocalStalkSections.neighbourhoodDiagram i x F) b
      have hU := ConcreteCategory.congr_hom
        (LocalStalkSections.ι_comparison i hi_inclusion x H hH F U) s
      have hV := ConcreteCategory.congr_hom
        (LocalStalkSections.ι_comparison i hi_inclusion x H hH F V) t
      have hst : (LocalStalkSections.cocone i hi_inclusion x H hH F).ι.app U s =
          (LocalStalkSections.cocone i hi_inclusion x H hH F).ι.app V t :=
        hU.symm.trans (hab.trans hV)
      exact Concrete.colimit_rep_eq_of_exists _ s t
        (localStalkSections_descent_equality i hi_inclusion x H hH F U V s t hst)
    · intro s
      obtain ⟨U, t, ht⟩ := localStalkSections_descent_sections i hi_inclusion x H hH F s
      refine ⟨colimit.ι (LocalStalkSections.neighbourhoodDiagram i x F) U t, ?_⟩
      exact (ConcreteCategory.congr_hom
        (LocalStalkSections.ι_comparison i hi_inclusion x H hH F U) t).trans ht
  exact ⟨NatIso.ofComponents (fun F ↦ asIso (c.app F)) (fun f ↦ c.naturality f)⟩
