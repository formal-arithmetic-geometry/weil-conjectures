/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.EssentiallySmall
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeaklyEtaleStability

/-!
# The small pro-étale site and its topos of sheaves

Source: blueprint main-20261015, chapter `sec-proetale-coefficients`, unit
`sk-def-sfb-finite-pushforward-pullback`, statement and proof of
`det-pe-topos-functoriality-site` (blueprint: det-pe-topos-functoriality-site).

The larger universe of the size convention is `u + 1`; in particular the topos clause
concerns sheaves of `Type (u + 1)`, with a site presentation in that same universe.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The pro-étale coverings satisfy the site axioms, representables are sheaves, and
set-valued sheaves form a Grothendieck topos in the larger universe.

Source: blueprint main-20261015, `det-pe-topos-functoriality-site`, clauses 1--3
and proof paragraphs 1--3; Stacks Project, Tags 022D, 023Q, 03A0 and 00XA
(blueprint: det-pe-topos-functoriality-site).

Proof:
1. Apply `lem-weil-pbc-fpqc-covering-axioms` to the underlying fpqc coverings.
   By `sk-lem-pe-weakly-etale-stability`, isomorphisms, composites, and base changes
   of the covering arrows are weakly étale. A base-change object remains weakly étale
   over the base scheme by composition. Fullness of the category over the base makes
   the scheme fibre product a fibre product in the small pro-étale category.
2. Apply `lem-weil-pbc-fpqc-representable-descent` to a compatible family of maps to
   a site object `T`. Apply uniqueness in that same descent statement with target `X`
   to see that the descended scheme map is over `X`. This proves existence and
   uniqueness of amalgamation for the representable, including an empty covering.
3. The size convention `def-weil-size-convention` and the definition of the small site
   place its objects and arrows in the larger universe. Choose its small skeleton.
   The induced topology and `lem-weil-pbc-site-equivalence-sheaf-transport` give an
   equivalence between sheaves on the original site and sheaves on this small site.
4. This site, its topology and the sheaf equivalence are exactly the presentation
   required by `def-weil-pbc-topos`; hence the final clause follows.
-/
theorem proetale_site_properties (X : Scheme.{u}) :
    (ProEt.precoverage X).IsSiteForCoverings ∧
      (ProEt.topology X).Subcanonical ∧
      EssentiallySmall.{u + 1} X.ProEt ∧
      IsGrothendieckTopos.{u + 1} (Sheaf (ProEt.topology X) (Type (u + 1))) := by
  have : MorphismProperty.IsStableUnderBaseChange @WeaklyEtale.{u} :=
    weaklyEtale_stability.1
  have : MorphismProperty.IsStableUnderComposition @WeaklyEtale.{u} :=
    weaklyEtale_stability.2.1
  have : (ProEt.precoverage X).HasIsos := by
    dsimp [ProEt.precoverage]
    infer_instance
  have : (ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [ProEt.precoverage]
    infer_instance
  have : (ProEt.precoverage X).IsStableUnderBaseChange := by
    dsimp [ProEt.precoverage]
    infer_instance
  have hsite : (ProEt.precoverage X).IsSiteForCoverings := by
    refine ⟨inferInstance, ?_, ?_⟩
    · exact (ProEt.precoverage X).toPretopology.transitive
    · intro I U V a hR Y b
      refine ⟨fun i ↦ Limits.pullback b (a i), fun i ↦ Limits.pullback.fst b (a i),
        fun i ↦ Limits.pullback.snd b (a i), ?_, ?_⟩
      · intro i
        exact IsPullback.of_hasPullback _ _
      · exact Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
          a hR b _ _ (fun i ↦ IsPullback.of_hasPullback _ _)
  refine ⟨hsite, inferInstance, inferInstance, ?_⟩
  let e := equivSmallModel.{u + 1} X.ProEt
  let K := e.inverse.inducedTopology (ProEt.topology X)
  exact ⟨SmallModel.{u + 1} X.ProEt, inferInstance, K,
    ⟨e.sheafCongr (ProEt.topology X) K (Type (u + 1))⟩⟩

end AlgebraicGeometry.Scheme
