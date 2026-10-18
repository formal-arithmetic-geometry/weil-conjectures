/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-!
# Classicality of pro-etale module sheaves is Zariski local

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-thm-pe-constructible-comparison-local`
(blueprint: det-pe-constructible-comparison-local).

As in the module comparison dependency, modules over the constant sheaf of a discrete
ring are encoded by sheaves valued in `ModuleCat`. Classicality is the existing predicate
on their underlying set sheaves. Open restriction is the existing sectionwise functor
`openImmersionRestriction`, not a choice of a local presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Classicality descends along any open covering, and restriction to any open subscheme
preserves classicality.

Source: Weil conjectures blueprint, main-20261015,
`sk-thm-pe-constructible-comparison-local`
(blueprint: det-pe-constructible-comparison-local).

Proof, following the four steps of the node:
1. The etale and pro-etale localization equivalences identify the sites over an open
   subscheme with the respective slice sites. In the presheaf-colimit formula for
   comparison inverse image, replace an etale object T by its intersection with the
   open subscheme. Inclusion is inverse on colimits, since restriction along this
   intersection gives the defining colimit relation. Coverings and refinements agree
   in the slice. The two plus constructions in
   lem-weil-pbc-sheafification-plus-theorem therefore commute with restriction.
   These identifications preserve addition and scalar action, and identify the
   restricted constant coefficient ring with the constant ring on the open subscheme.
   Thus comparison inverse image commutes with open restriction. The essential-image
   characterization in det-pe-classical-sheaves-modules proves the converse clause.
2. For classical restrictions, choose local etale module models and comparison
   isomorphisms using det-pe-classical-sheaves-modules. On each double intersection,
   full faithfulness uniquely lifts the transition isomorphism to a linear isomorphism
   between the etale models. Faithfulness on triple intersections gives the cocycle
   identity; uniqueness gives identity transitions for repeated indices.
3. Apply lem-weil-pbc-site-module-sheaf-gluing on the etale site to the open cover,
   its constant coefficient ring, and this descent datum. The slice identifications
   and coefficient restriction from step 1 identify all local categories. Obtain an
   etale module sheaf F₀ and compatible local identifications with the chosen models.
4. Apply comparison inverse image to these identifications and compose with the local
   comparison isomorphisms. The cocycle equations make the resulting maps agree on
   overlaps. An open cover is pro-etale by sk-def-pe-site. Apply
   lem-pur-sheaf-hom-cover-gluing to glue these linear maps and their agreeing inverses.
   Uniqueness makes both composites identities, so the global sheaf is isomorphic to
   the comparison inverse image of F₀ and is classical by
   det-pe-classical-sheaves-modules. -/
theorem proEtaleClassical_zariskiLocal (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (∀ (I : Type w) (U : I → X.Opens), (⨆ i : I, U i) = ⊤ →
      (∀ i : I, IsClassical
        ((sheafCompose (Scheme.ProEt.topology (U i).toScheme)
          (forget (ModuleCat.{u + 1} Λ))).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} Λ) (U i).ι).obj F))) →
      IsClassical
        ((sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))).obj F)) ∧
    (IsClassical
        ((sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))).obj F) →
      ∀ U : X.Opens, IsClassical
        ((sheafCompose (Scheme.ProEt.topology U.toScheme)
          (forget (ModuleCat.{u + 1} Λ))).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} Λ) U.ι).obj F))) := by
  sorry

end AlgebraicGeometry.ProEtale
