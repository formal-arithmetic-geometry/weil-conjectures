/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module
public import Sheaf.AlgebraicGeometry.GrothendieckEtaleSectionSystemLaws
import Sheaf.Paper.EtaleFiniteDataDescent
/-! # Degree-zero continuity on the qcqs étale basis -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Canonical relative section cocones are colimiting on qcqs étale objects.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2;
Stacks Project, Étale Cohomology, Tag 09YQ, degree zero, and Sites, Tag 0738(4).
The categorical coefficient generalization is the finite-equalizer argument below.

Proof: the over category of i is cofiltered and initial over I, so the restricted
cone is still a limit. On the qcqs finite-presentation étale basis, descent of
objects, morphisms, equalities of morphisms, and finite covers identifies the
limit basis with the filtered colimit of the stage bases. The inverse-image
presheaf associated to G restricts on that basis to the pointwise filtered
colimit of the displayed stage section presheaves. Refine each cover of a qcqs
object to a finite affine cover. Intersections are qcqs because the objects are
quasi-separated. The sheaf matching condition is a finite equalizer between
finite products over the cover and pairwise overlaps. AB5 in A commutes these
finite limits with the filtered colimit. Thus this pointwise colimit is already
a sheaf on the basis, so the inverse-image universal property identifies it
with (c.π_i)^*G there. Naturality of the adjunction unit and the specified
composition isomorphisms identify the comparison with relativeSectionCocone,
not an arbitrary isomorphic cocone. Its evaluation at U is therefore a colimit.
The empty covering gives the terminal (zero) object; the argument includes
empty schemes and empty U, and uses no cohomology or resolution.
(blueprint: lem-weil-pbc-grothendieck-etale-relative-section-colimit) -/
theorem relativeSectionCocone_isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (i : I) (G : Sheaf (D.obj i).smallEtaleTopology A)
    (U : (D.obj i).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
      (relativeSectionCocone A D c i G))) := by sorry

end AlgebraicGeometry.Etale
