/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparisonCore
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparisonIso

/-! # Degree-zero continuity for etale sections

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Stalkwise sections factor through inverse image to the local scheme and its
section functor. This comparison requires no henselianity. -/
theorem strictHenselian_stalkSections_comparison
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X) :
    ∃ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
        Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1},
      H.PreservesEpimorphisms ∧
        Nonempty (etaleObjectStalkSections X i x ≅
          H ⋙ (sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 _)))) := by
  obtain ⟨H, ⟨adj⟩⟩ := strictHenselian_stalkSections_comparison_functor (X.fromSpecStalk x)
  exact ⟨H, Functor.preservesEpimorphisms_of_adjunction adj,
    strictHenselian_stalkSections_comparison_iso i hi_inclusion x H adj⟩
