/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RepleteSheafTopos
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteOnContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite

/-!
# Repleteness of the pro-étale topos

## References

* Bhatt–Scholze, *The pro-étale topology*, Proposition 4.2.8.
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- **Repleteness of the pro-étale topos**. For every scheme, the topos of set-valued sheaves
on its small pro-étale site is replete: inverse sequences with epimorphic transition maps have
epimorphic limit projections at every natural-number index. -/
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X) := by
  intro F hF m
  apply (CategoryTheory.Sheaf.isLocallySurjective_iff_epi _).1
  constructor
  intro U y
  obtain ⟨I, W, f, hW, hcov⟩ := ProEt.exists_isWContractibleRing_cover U
  apply (ProEt.topology X).superset_covering _ hcov
  rintro V g ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨D, hD, ⟨e⟩⟩ := hW i
  have : IsWContractibleRing D := hD
  have hw : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} (W i) :=
    ProEt.isWeaklyContractible_of_iso e
  exact (CategoryTheory.Presheaf.imageSieve _ y).downward_closed
    ((proetale_surjective_sections_of_epi_tower X F hF (W i) hw).2 m _) a

end AlgebraicGeometry.Scheme
