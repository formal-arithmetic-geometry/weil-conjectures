/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

/-! # Local sections after sheafification
Source: literature/stacks-project/sites.tex, Sites, Theorem 00WB and Lemma 00WK
(blueprint: lem-weil-pbc-site-sheafification-sections-local)
-/

-- The unit is locally surjective even without a relation between u and w:
-- its locally generated image is a subsheaf of its target, and the universal
-- property provides a retraction of that image's inclusion.
private theorem unit_locally_surjective
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [HasWeakSheafify K (Type w)] (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective K (toSheafify K F) := by
  let G := sheafify K F
  let η := toSheafify K F
  have hG : Presheaf.IsSheaf K G := (presheafToSheaf K (Type w)).obj F |>.property
  have hG' := (isSheaf_iff_isSheaf_of_type K G).mp hG
  let R := (Subfunctor.range η).sheafify K
  have hR : Presheaf.IsSheaf K R.toFunctor :=
    (isSheaf_iff_isSheaf_of_type K R.toFunctor).mpr
      ((Subfunctor.range η).sheafify_isSheaf hG')
  let l := sheafifyLift K (Subfunctor.toRangeSheafify K η) hR
  have hl : l ≫ R.ι = 𝟙 G := by
    apply sheafify_hom_ext K _ _ hG
    dsimp [l]
    rw [← Category.assoc, toSheafify_sheafifyLift]
    simp [Subfunctor.toRangeSheafify, R, η, G]
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro U s _
  have e : (l.app U s).val = s := by
    have := congrArg (fun t ↦ t.app U s) hl
    simpa [G] using this
  exact e ▸ (l.app U s).property

-- Source: Stacks Project, Sites, Lemma 00WK, local representability.
-- Extract a precoverage cover inside the unit's covering image sieve,
-- then choose a preimage on each covering arrow.

-- Source: Stacks Project, Sites, Lemma 00WK, converse. Local agreement
-- maps to local agreement in G; separatedness gives compatibility, and
-- the sheaf condition glues the family uniquely.

end CategoryTheory
