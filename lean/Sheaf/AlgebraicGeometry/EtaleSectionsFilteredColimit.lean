/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Filtered colimits of sections on quasi-compact quasi-separated etale objects

Source: Sites, Lemma 7.17.7, Tag 0738, part (4), applied using Etale Cohomology,
Section 59.51, Tag 03Q4 (blueprint: lem-weil-pbc-etale-qcqs-sections-filtered-colimit).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Sections over a quasi-compact quasi-separated scheme in the small etale site commute
with filtered colimits of sheaves of modules. The comparison is the unique map whose
composite with each colimit coprojection is the corresponding cocone map evaluated at `U`.
Source: Sites, Lemma 7.17.7, Tag 0738, part (4), and Etale Cohomology, Tag 03Q4
(blueprint: lem-weil-pbc-etale-qcqs-sections-filtered-colimit).

Proof:
1. By `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`, every covering of `U` has a
   cofinal finite affine etale refinement with quasi-compact pairwise fibre products.
2. Set `P(V) = colim_i G_i(V)`. By `lem-weil-pbc-module-sheaves-colimits-forgetful`, the
   underlying sheaf colimit is the sheafification of `P`. Two representatives with equal
   images agree locally by `lem-weil-pbc-site-sheafification-sections-local`. Refine this
   witness to a finite cover. By `lem-weil-pbc-filtered-colimit-sets-elementwise`, equality
   on each member is eventual; filteredness gives a common index. The sheaf equalizer
   condition `lem-weil-pbc-pretopology-sheaf-condition` gives equality over `U`, proving
   injectivity. This argument needs only quasi-compactness and applies to the overlaps.
3. A section of the colimit is locally represented in `P`, by the same local
   sheafification node. Use Step 1 to obtain finitely many representatives in the `G_i`.
   Their images agree on each quasi-compact overlap. Step 2 and eventual equality give
   indices where their restrictions agree. Filteredness gives one index dominating these
   finitely many choices (and equalizing the finitely many transition arrows). The sheaf
   condition glues them to a section over `U`, proving surjectivity. The forgetful-colimit
   node identifies the underlying-set and module colimits, so the comparison is bijective.
-/
theorem etale_sections_filtered_colimit
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (_hc : IsColimit c) :
    let E := (sheafSections X.smallEtaleTopology (ModuleCat.{max v w} Λ)).obj
      (Opposite.op U)
    Function.Bijective ((colimit.desc (G ⋙ E) (E.mapCocone c)).hom) := by
  sorry

end AlgebraicGeometry
