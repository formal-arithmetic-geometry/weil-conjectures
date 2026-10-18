/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.RingTheory.IndEtaleStability

/-!
# Enough points of the small pro-étale topos

Source: Stacks Project, Pro-étale Cohomology, Tag 0992, `lemma-points-proetale`
(blueprint: lem-sfb-proetale-enough-points).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- The small pro-étale topos of any scheme has a set-indexed conservative family
of points. Source: Stacks Project, Tag 0992, `lemma-points-proetale`
(blueprint: lem-sfb-proetale-enough-points).

The site has objects in universe `u + 1` and morphisms in universe `u`; sheaves
and points take values in `Type (max (u + 1) v)`, allowing any compatible larger
universe. A small skeleton can be chosen in that universe. Points here are the
geometric morphisms of def-trf-geometric-morphism, not ordinary geometric points
of the scheme.

Proof of the node, following Stacks 0992:
1. Restrict to the full subsite of affine weakly étale objects with standard
   finite affine covers. Restriction is an equivalence by
   lem-sfb-proetale-affine-subsite-equivalence (Stacks 098W).
2. The coproduct of all sheafified representables maps epimorphically to the
   terminal sheaf: two maps out of the terminal sheaf agreeing after this map
   agree at the identity of every object, via the sheafification unit, hence
   agree as natural transformations. This uses def-weil-pbc-sheafification and
   def-weil-pbc-sites-and-cohomology and does not require subcanonicity.
3. Each affine slice has pullbacks: the scheme fibre product is affine by
   lem-weil-pbc-fibre-product-affine-spectra. Its arrows remain weakly étale by
   lem-trf-weakly-etale-between-objects and lem-weil-pbc-ind-etale-stability.
   The scheme universal property restricts to the full affine slice.
4. The identity object is terminal in each slice; apply
   lem-weil-pbc-finite-limits-from-terminal-pullbacks. The standard affine
   covering families are finite, so each refines itself, including the empty
   cover of the empty scheme. No quasi-compactness assumption on X is needed.
5. Apply lem-sfb-site-finitary-slice-enough-points (Stacks 00YN) and transport
   its conservative family through the equivalence of step 1. The inverse
   equivalence preserves finite limits and has an adjoint. Composition of
   geometric morphisms thus gives the stated points. If all inverse images
   of a morphism are bijective, its restriction is invertible by conservativity,
   and the equivalence reflects its invertibility.
-/
theorem proEtale_enoughPoints (X : Scheme.{u}) :
    ∃ (ι : Type (max (u + 1) v))
      (p : ι → GeometricMorphism (Type (max (u + 1) v))
        (Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))),
      ∀ {F G : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  sorry

end AlgebraicGeometry
