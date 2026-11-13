/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites

/-!
# Exactness of pullback from the Zariski site to the small étale site

Pullback of abelian sheaves along a continuous lift of open restriction from the Zariski site to
the small étale site preserves finite limits.

## References

* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction
/-- Abelian pullback along an open-restriction lift preserves finite limits. -/
theorem zariski_etale_pushed_resolution_finite_limits
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    :
    PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) := by
  let := hi
  obtain ⟨j, hj, _, hjlim, _, _⟩ := zariski_to_etale_is_morphism.{u + 1, 0} X
  let e : i ≅ j := Functor.fullyFaithfulCancelRight (Scheme.Etale.forget X)
    (eqToIso (hi_inclusion.trans hj.symm))
  have : PreservesFiniteLimits j := hjlim
  have : PreservesFiniteLimits i := preservesFiniteLimits_of_natIso e.symm
  have : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  have : PreservesFiniteLimits (i.op.lan :
      (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    preservesFiniteLimits_op_lan_of_flat i
  unfold sheafPullback
  exact comp_preservesFiniteLimits _ _
