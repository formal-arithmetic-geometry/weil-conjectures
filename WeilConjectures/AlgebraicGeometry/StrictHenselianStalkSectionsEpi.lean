/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparison
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Local lifting of etale sections

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- At a strictly henselian point, stalkwise sections preserve epimorphisms. -/
theorem strictHenselian_stalkSections_preservesEpimorphisms
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (x : X) (hx : IsStrictlyHenselianLocalRing (X.presheaf.stalk x)) :
    (etaleObjectStalkSections X i x).PreservesEpimorphisms := by
  obtain ⟨H, hH, ⟨e⟩⟩ := strictHenselian_stalkSections_comparison i hi_inclusion x
  let := hH
  have : ((sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 _)))).PreservesEpimorphisms := by
    let : IsStrictlyHenselianLocalRing (X.presheaf.stalk x) := hx
    refine ⟨?_⟩
    intro F G φ hφ
    exact (AddCommGrpCat.epi_iff_surjective _).2
      (Scheme.surjective_app_of_epi_of_isStrictlyHenselianLocalRing
        (X.presheaf.stalk x) φ)
  exact Functor.PreservesEpimorphisms.of_iso e.symm
