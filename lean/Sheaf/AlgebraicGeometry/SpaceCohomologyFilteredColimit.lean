module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.SiteFiniteCoverCohomologyColimit
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.EquivalenceDerivedSections

/-! # Filtered colimits of étale cohomology on algebraic spaces

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 073E, `lemma-colimits`
(blueprint: lem-sfb-space-cohomology-filtered-colimit).

The cohomology functor is the global abelian-sheaf cohomology functor on the recorded
small étale site. The comparison is induced by the coprojections of the colimit in
abelian sheaves, rather than by a colimit of the underlying presheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- On a quasi-compact and absolutely quasi-separated algebraic space, global étale
cohomology commutes with small filtered colimits of abelian sheaves in every degree.
The coefficient universe `w` is arbitrary: it covers the project's abelian sheaves with
sections in the universe of `S` (`w = u`, sheafification by `etaleAlgebraModulesHasSheafify`)
and larger coefficient universes (`w ≥ u + 1`, sheafification by Mathlib). The
`HasSheafify` and `HasExt` parameters are these existence statements (propositions, no
chosen data); `HasExt` fixes the standard model of Ext groups in the universe of the
morphisms of abelian sheaves, which exists by enough injectives. Neither is a geometric
assumption.

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 073E, `lemma-colimits`
(blueprint: lem-sfb-space-cohomology-filtered-colimit).

Proof:
1. Enlarge the small étale site to algebraic spaces étale over X. By
   lem-trf-space-enlarged-site-scheme-density, restriction along scheme objects is an
   equivalence on set sheaves. Transport addition, zero and inverse through this
   fully faithful finite-product-preserving equivalence to obtain an additive
   equivalence on abelian sheaves. It identifies the global-section functors.
2. Use the qcqs objects as B and their finite qcqs coverings as Cov_0. Given any
   covering of U in B, refine it by affine scheme components using
   lem-a1-space-affine-etale-cover. Their composites are étale by
   lem-trf-space-chartwise-etale-permanence and have open point images. Compactness
   of U selects finitely many components. Each remains over its original covering
   member and is qcqs by lem-weil-pbc-affine-scheme-qcqs. For empty U use the empty cover.
3. All positive-length iterated intersections, allowing repetitions, are qcqs by
   repeated application of lem-sfb-qcqs-space-fibre-product, with the same qcqs base U.
   They remain étale over X by lem-trf-space-chartwise-etale-permanence.
4. Apply lem-sfb-site-finite-cover-cohomology-colimit. The terminal object X/X is in B
   by the two given hypotheses, so the result at this object is global cohomology.
5. Both abelian sheaf categories have enough injectives by
   lem-weil-pbc-site-sheaves-enough-injectives. Apply
   lem-exc-equivalence-derived-sections to transport cohomology back. The equivalence
   preserves colimits and their legs. Naturality identifies each transported leg
   with cohomology of the corresponding sheaf coprojection. Uniqueness in
   def-weil-pbc-category-colimit identifies the comparison with `colimit.post`. -/
theorem isIso_cohomology_filteredColimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    [HasSheafify X.etaleTopology AddCommGrpCat.{w}]
    [HasExt.{max (u + 1) w} (Sheaf X.etaleTopology AddCommGrpCat.{w})]
    (D : Type w) [SmallCategory D] [IsFiltered D]
    (F : D ⥤ Sheaf X.etaleTopology AddCommGrpCat.{w}) (q : ℕ) :
    IsIso (colimit.post F (Sheaf.functorH.{max (u + 1) w, w} X.etaleTopology q)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
