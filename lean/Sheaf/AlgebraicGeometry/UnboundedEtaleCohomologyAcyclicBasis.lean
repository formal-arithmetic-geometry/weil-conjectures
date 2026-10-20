/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.SiteRestrictionInjectives
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.CategoryTheory.TruncationHypercohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.Filtration
import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
import Sheaf.CategoryTheory.SiteTruncationDerivedLimit
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-!
# Unbounded étale cohomology on an acyclic covering class

Source: Stacks Project, Tag 0BKZ, `sites-cohomology.tex`,
`lemma-cohomology-over-U-trivial`, specialized to abelian sheaves on the small étale site
(blueprint: lem-kun-0bkz).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Unbounded hypercohomology over an étale object in an acyclic covering class agrees
with sections of the corresponding cohomology sheaf. The equality in the source means an
isomorphism of abelian groups. Restriction of `K` to `U.left` is exact étale pullback;
`Sheaf.H` computes ordinary cohomology after restriction to `U.left`, and degree zero is
written as evaluation of the sheaf at `U`.

Source: Stacks Project, Tag 0BKZ, `lemma-cohomology-over-U-trivial`
(blueprint: lem-kun-0bkz).

Proof:
1. Work with abelian sheaves as modules over the constant integer sheaf, using
   def-weil-size-convention, def-weil-pbc-constant-sheaf and
   def-weil-sheaf-of-modules-category. Cohomology over `U` is derived evaluation:
   lem-weil-pbc-site-restriction-injectives makes slice restriction exact,
   lem-pur-kinjective-restrict-localized preserves K-injectives, and
   lem-weil-pbc-etale-site-localization-open identifies the slice with `U.left`'s étale
   site. Thus def-kun-rgamma-unbounded computes the same sections complex.
2. For `Kₙ = τ≥(-n) K`, def-kun-truncations identifies its cohomology sheaves with those
   of `K` in degrees at least `-n`, and zero below. Apply thm-sp-truncation-e2 to these
   bounded-below complexes and evaluation at `U`. The Grothendieck and K-injective
   existence input is prop-pur-kinjective-resolutions-exist, also for abelian groups.
3. The acyclicity hypothesis kills all positive columns of these spectral sequences;
   negative columns are zero. All differentials to or from column zero vanish. The
   finite abutment filtration therefore identifies cohomology with sections of the
   cohomology sheaf. Naturality of the truncations, pages and edge maps makes these
   identifications commute with the tower transitions.
4. Apply lem-kun-site-truncation-derived-limit with bound zero. Its local vanishing
   and covering hypotheses are exactly the two assumptions here, so `K` is the derived
   limit of the `Kₙ`, with their canonical projections.
5. By lem-kun-site-rgamma-derived-limit, derived sections preserve this derived limit.
   Apply lem-pc-derived-limit-milnor-sequence to get the short exact sequence with
   left term `R¹ lim H^(q-1)(U,Kₙ)` and right term `lim H^q(U,Kₙ)`.
6. Once `n ≥ 1-q`, both cohomology towers in that sequence identify with the constant
   groups of sections of `H^(q-1)(K)` and `H^q(K)`; their transition maps are identities.
7. Use lem-pc-derived-limit-roos-abelian-groups: the limit and first derived limit are
   the kernel and cokernel of `1-shift` on the product. On an eventually constant tower,
   this map is surjective, by choosing zero at a fixed tail index, solving successively
   forwards using inverse transitions, and backwards using transitions. Its kernel is
   the common tail value. The Milnor sequence now gives the claimed isomorphism.
-/
theorem cohomology_iso_sections_of_acyclic_covering_class (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (B : Set X.Etale)
    (hcover : ∀ V : X.Etale,
      ∃ (ι : Type (u + 1)) (W : ι → X.Etale) (f : ∀ i : ι, W i ⟶ V),
        (∀ i : ι, W i ∈ B) ∧ Sieve.ofArrows W f ∈ X.smallEtaleTopology V)
    (hacyclic : ∀ (U : X.Etale), U ∈ B → ∀ (p : ℕ), 0 < p → ∀ q : ℤ,
      Subsingleton (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} U.hom).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K)) p)) :
    ∀ (U : X.Etale), U ∈ B → ∀ q : ℤ,
      Nonempty
        ((cohomology AddCommGrpCat.{u + 1} U.left q).obj
            ((upperStar AddCommGrpCat.{u + 1} U.hom).mapDerivedCategory.obj K) ≅
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj K).obj.obj (op U)) := by
  sorry

end AlgebraicGeometry.Etale
