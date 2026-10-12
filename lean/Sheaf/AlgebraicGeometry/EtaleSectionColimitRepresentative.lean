/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleSectionColimitEventualZero
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-! # Stage representatives in filtered etale sheaf colimits

Source: Stacks Project, Sites, Lemma Tag 0738, and Etale Cohomology, Tag 03Q4.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every section of a filtered colimit of module sheaves over a qcqs etale object
comes from a section at a diagram stage.
Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (4), and Etale
Cohomology, Section Tag 03Q4 (blueprint: lem-weil-pbc-etale-section-colimit-representative).

Proof: Identify c.pt with the module sheafification of the sectionwise presheaf
colimit P, respecting the coprojections. A section t is locally represented in P.
Refine the local representing covering to a finite affine etale covering of U
with quasi-compact pairwise fibre products, using the qcqs finite-refinement lemma.
Choose a stage representative on each member. Filteredness puts the finitely many
representatives at one stage. On each pairwise fibre product their difference has
zero image in c.pt, as both images restrict from t. Apply the eventual-zero theorem
on that quasi-compact overlap. Choose a stage dominating the finitely many killing
arrows, equalizing the finitely many arrows from the common initial stage. The
transported representatives now agree on all overlaps. The sheaf condition at this
stage glues them to a section s over U. Its colimit image is t because this holds
on every covering member and c.pt is separated. Empty covers cause no exception:
the sheaf condition gives the unique zero section, and filteredness supplies an index. -/
theorem etale_section_colimit_representative
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) :
    ∀ t : c.pt.obj.obj (Opposite.op U),
      ∃ (i : I) (s : (G.obj i).obj.obj (Opposite.op U)),
        ((c.ι.app i).hom.app (Opposite.op U)).hom s = t := by
  sorry

end AlgebraicGeometry
