module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# The inclusion of the Zariski site into the small étale site

Source: literature/stacks-project/sites.tex, Proposition Tag 00X6 and
Lemma Tag 00X5 (blueprint: lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites)

## Main statements

* `zariski_to_etale_is_morphism` records the inclusion functor, its continuity,
  preservation of finite limits, and exact sheaf inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- The inclusion of the Zariski site into the small étale site is a morphism of sites.

Source: literature/stacks-project/sites.tex, Proposition Tag 00X6 and
Lemma Tag 00X5 (blueprint: lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites).
Proof (the seven steps of the node):
1. Open immersions are étale (`lem-weil-pbc-open-immersion-etale`), so send an
   open to its inclusion and an inclusion to the corresponding morphism over `X`.
   Identities and composition are those of inclusions.
2. The top open is terminal, and intersections are pullbacks in the poset of opens
   (`def-sc-zariski-site`).
3. The identity of `X` is terminal in the small étale site, and its pullbacks are
   scheme pullbacks (`lem-weil-pbc-etale-base-change-finite-limits`). Intersections
   compute these pullbacks by `lem-weil-pbc-open-preimage-fibre-product`; uniqueness
   of limits gives the canonical comparison isomorphisms.
4. A jointly surjective open family remains jointly surjective and étale. Together
   with step 3 this gives Stacks continuity (`def-weil-pbc-sites-and-cohomology`).
5. Precomposition sends sheaves to sheaves
   (`lem-weil-pbc-site-continuous-pushforward-sheaf`). Sheafified presheaf pullback
   is its left adjoint (`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`),
   hence preserves colimits (`lem-weil-pbc-left-adjoint-preserves-colimits`).
6. The inclusion of sheaves preserves finite limits
   (`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`); presheaf pullback does too,
   by steps 2 and 3 (`lem-weil-pbc-presheaf-pullback-sets-left-exact`), as does
   sheafification (`lem-weil-pbc-sheafification-sets-exact`). Their composite is
   the left adjoint, so it preserves finite limits.
7. This exact left adjoint and sectionwise precomposition give the required
   morphism of sites, inverse image, direct image and adjunction
   (`def-weil-pbc-sites-and-cohomology`).
-/
theorem zariski_to_etale_is_morphism (X : Scheme.{u}) :
    ∃ (i : X.Opens ⥤ X.Etale),
      (i ⋙ Scheme.Etale.forget X = X.restrictFunctor) ∧
      CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i ∧
      PreservesFiniteLimits i ∧
      Nonempty (IsTerminal (i.obj ⊤)) ∧
      ∃ (_ : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology),
        ∃ (L : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) ⥤
            Sheaf X.smallEtaleTopology (Type (max (u + 1) v))),
          Nonempty (L ⊣ i.sheafPushforwardContinuous (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) ∧
          PreservesFiniteLimits L ∧ PreservesFiniteColimits L := by
  sorry

end AlgebraicGeometry
