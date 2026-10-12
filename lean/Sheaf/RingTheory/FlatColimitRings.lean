/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings

/-!
# Flatness over a filtered colimit of commutative rings

Source: Stacks Project, Algebra, Tag 05UU (1), with the module equal to the target ring;
Categories, Tag 0032, for filtered reindexing (blueprint: lem-weil-pbc-colimit-rings-flat).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingHom

/-- A ring map out of a filtered colimit is flat if its composite with every coprojection
is flat. Source: Stacks Project, Algebra, Tag 05UU (1), specialized to the target ring,
and Categories, Tag 0032 (blueprint: lem-weil-pbc-colimit-rings-flat).

Proof:
1. Reindex the filtered diagram by a nonempty directed set using
   `lem-weil-pbc-cofiltered-limit-directed-reindex` on the opposite diagram.
2. By `lem-weil-pbc-flat-fg-ideal-criterion`, it suffices to prove injectivity of
   the multiplication map from each finitely generated ideal tensored with the target.
3. Descend the generators to one stage using
   `lem-weil-pbc-filtered-colimit-algebras-elementwise`. Restrict to the cofinal upper
   set using `lem-weil-pbc-colimit-initial-full-subcategory`, and extend that stage's
   ideal to all later stages.
4. These ideals have the given ideal as their colimit in abelian groups: elements
   descend to a stage and equalities hold eventually by
   `lem-weil-pbc-filtered-colimit-rings-zero`. The same holds for the rings themselves;
   their induced module action on the ideal is multiplication.
5. Apply `lem-weil-pbc-filtered-colimit-tensor-varying-rings` to the ideals and the
   constant target system. Identify the latter colimit by
   `lem-weil-pbc-colimit-constant-connected-diagram`.
6. Each stage's multiplication map is injective because the target is flat over that
   stage, as expressed by `def-weil-pbc-flat-ring-map`.
7. By `lem-weil-pbc-filtered-colimit-abelian-groups-exact`, their colimit map is injective.
   The tensor comparison identifies this map with the multiplication map in step 2,
   proving flatness. -/
theorem flat_of_flat_comp_colimit_ι {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] {S : Type v} [CommRing S]
    (ψ : ↥(colimit F) →+* S)
    (hψ : ∀ i : I, (ψ.comp (colimit.ι F i).hom).Flat) : ψ.Flat := by
  sorry

end RingHom
