/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.CompletedCondensedCoefficients

/-!
# Finite coefficient descent on quasi-compact pro-étale objects

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-sections;
Stacks Project, Sites, Tag 0738 (blueprint: det-lem-coefficient-finite-descent-sections).

The three statements give clause (1) for sets and abelian groups and clause (2)
for the existing finite-subextension coefficient sheaves. No quasi-separatedness
is imposed in the injective-transition case or in coefficient descent.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The section-colimit comparison for sets is injective on a quasi-compact object,
and bijective if the object is quasi-separated or all transitions are sectionwise injective.
The sheaf colimit is supplied as an arbitrary cocone `c` with universal property `hc`.
Source: Stacks Project, Sites, Tag 0738(2)--(4), and the corrected blueprint node
(blueprint: det-lem-coefficient-finite-descent-sections), clause (1).

Proof: (1) Form the sectionwise presheaf colimit; sheafification is the sheaf colimit
by its adjunction (lem-weil-pbc-presheaf-colimits-sectionwise,
def-weil-pbc-sheafification). Filteredness gives representatives and eventual equality,
including equalization of parallel arrows (def-weil-pbc-category-colimit).
(2) An fpqc covering of a quasi-compact pro-etale object has a finite affine refinement
(sk-def-pe-site, def-weil-pbc-quasi-compact-scheme, def-weil-pbc-sites-and-cohomology).
(3) Equal images are equal locally by lem-weil-pbc-site-sheafification-sections-local.
On the finite refinement, move the equality witnesses to a common stage and use the
stage sheaf's separatedness. This proves injectivity.
(4) For a quasi-separated object, pairwise overlaps of affine covering objects are
quasi-compact: base change its quasi-compact diagonal to their affine product over Z
(def-weil-quasi-separated-morphism, lem-pc-quasi-compact-base-change,
lem-weil-pbc-fibre-product-affine-spectra). Lift a section locally, refine finitely,
move to a common stage, and use (3) on the finitely many overlaps. A further common
stage makes the representatives compatible, and the sheaf condition glues them.
(5) Alternatively, injective transitions make every stage inject into its presheaf
colimit, using filteredness to equalize parallel arrows. Local equality and the stage
sheaf condition then make every stage inject into the sheaf colimit on every object.
Move local representatives on a finite cover to one stage; they agree on all overlaps
by this injectivity and glue, without assuming quasi-compact overlaps. -/
theorem set_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          (Type (max (u + 1) v))).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            (Type (max (u + 1) v))).obj (op V)).mapCocone c))) := by
  sorry

/-- The same section-colimit comparison for abelian sheaves, with the same two
sufficient conditions for bijectivity. In both comparisons, `c` with `hc` is an
arbitrary chosen sheaf-colimit cocone; the source is the chosen section-group colimit.
Source: Stacks Project, Sites, Tags 0738 and 03CO(4), and blueprint clause (1)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: Use the set comparison just stated (steps (1)--(5) of this node).
The presheaf colimit is sectionwise (lem-weil-pbc-presheaf-colimits-sectionwise),
and forgetting abelian groups preserves filtered colimits
(lem-weil-pbc-abelian-groups-forget-filtered-colimits).
Abelian sheafification has the underlying set sheafification
(lem-pc-sites-sheafification-underlying-sets), so the underlying comparison is
precisely the set comparison, with unchanged compactness and transition hypotheses.
This also agrees with the abelian sheaf colimit of
lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact. -/
theorem abelian_sections_filtered_colimit (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (c : Cocone F) (hc : IsColimit c) :
    Function.Injective
        (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
          AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c)) ∧
      ((QuasiSeparated (toSpecZ V.left) ∨
          ∀ (i j : I) (f : i ⟶ j) (U : X.ProEt),
            Function.Injective ((F.map f).hom.app (op U))) →
        Function.Bijective
          (colimit.desc _ (((sheafSections (Scheme.ProEt.topology X)
            AddCommGrpCat.{max (u + 1) v}).obj (op V)).mapCocone c))) := by
  sorry

/-- Coefficient inclusions are injective on sections, their ranges cover the algebraic
closure coefficient sections, and every finite set or finite family of finite matrices
has entries in one finite subextension. No quasi-separatedness is required.
Source: blueprint main-20261015, coefficient finite descent, clause (2)
(blueprint: det-lem-coefficient-finite-descent-sections).

Proof: (7) The condensed finite-field inclusions are injective on sections, since they
postcompose continuous functions with field inclusions (sk-def-sfb-condensed-ring,
def-sfb-subfield-coefficient-map). Pullback from the point preserves this injectivity:
the test functor preserves finite limits and coverings (sk-def-sfb-pullback-from-point),
so its inverse image is exact by lem-weil-pbc-left-exact-site-inverse-image-tensor;
scheme inverse image is exact by det-pe-topos-functoriality-inverse-image.
The composite p_X^* is exact, and sections are left exact
(def-weil-pbc-sites-and-cohomology), giving injective coefficient transitions.
(8) Use the finite-subextension ring-sheaf colimit of sk-prop-sfb-qlbar-colimit-x,
not its separate rationalization comparison. The injective-transition proof of (1)
applies also to ring sheaves, since filtered ring colimits and ring sheafification
have the same underlying set constructions. Thus the sections are the filtered
colimit of the finite-field sections. Eventual equality and the injective transitions
make its stage maps injective and identify it with their union.
(9) For each member of a finite set choose a stage representative, and take a common
upper bound in the directed nonempty poset of finite subextensions
(sk-def-sfb-qlbar-condensed). For matrices use the finite set of all entries.
For the empty set, empty matrix family, or empty matrix dimensions, the base field
is an available finite subextension. -/
theorem coefficient_finite_descent_sections (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (V : X.ProEt) [CompactSpace V.left] :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Function.Injective ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (Set.univ = ⋃ E : PadicAlgCl.FiniteIntermediateField l,
      Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ S : Set ((padicAlgClRingObj X l).obj.obj (op V)), S.Finite →
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        S ⊆ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) ∧
    (∀ (K : Type v) [Finite K] (rows : K → Type w) (cols : K → Type z)
      [∀ k : K, Finite (rows k)] [∀ k : K, Finite (cols k)]
      (M : ∀ k : K, Matrix (rows k) (cols k)
        ((padicAlgClRingObj X l).obj.obj (op V))),
      ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ (k : K) (i : rows k) (j : cols k),
          M k i j ∈ Set.range ((padicSubfieldRingObjToPadicAlgCl X l E).hom.app (op V))) := by
  sorry

end AlgebraicGeometry.ProEtale
