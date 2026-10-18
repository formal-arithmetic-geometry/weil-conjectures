/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Sheaf.CategoryTheory.PointSystemRefineAll
import Sheaf.CategoryTheory.Sites.PointFamilyConservative
import Sheaf.TraceFormula.InverseSystemSitePoint

/-!
# Finite-cover sites with finite limits have enough points

Source: Stacks Project, Sites, Tag 00YQ, Proposition `proposition-criterion-points`
(blueprint: lem-trf-finitary-site-enough-points).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A small site with finite limits and finite covering refinements has a
set-indexed conservative family of points. Source: Stacks Project, Sites, Tag 00YQ
(blueprint: lem-trf-finitary-site-enough-points).

The sheaves take values in `Type (max u w)`, a universe containing the site's
universe `u`: in the source the site is a set and its sheaves are valued in all sets
(size convention, def-weil-size-convention). With values in a universe below `u` the
conclusion fails, e.g. for presheaves on a meet-semilattice with an antichain of
size larger than the value universe.

The proof follows the node. Step 1: fix a sheaf `F`, an object `U` and distinct
sections `s ≠ s'` of `F(U)`; starting from the one-element system at `U`, apply the
all-at-once refinement (Stacks 00YP) countably often and take the union of the
chain; the images of `s, s'` stay distinct (equality in a directed colimit is
witnessed at one index), and every element of the final `u(W)` lifts along every
finite covering `{W_k → W}`. Step 2: by the finite-refinement hypothesis the
lifting holds for every covering, and finite limits in `C` make `u` left exact, so
the system defines a point (Stacks 00YC, 00YA) in whose stalk `s, s'` stay
distinct. Step 3: the point depends only on the inverse system in `C`, and the
systems produced have index posets bounded in size in terms of `C`, so up to
isomorphism they form a set in universe `u`; one point for each of them gives the
index type `ι`, and since every distinct pair of sections is separated by one of
these points, the point-family criterion (Stacks 00YM) gives joint reflection of
isomorphisms.
-/
theorem finitarySite_enoughPoints
    {C : Type u} [SmallCategory C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (hfinite : ∀ (X : C) (I : Type (max u v)) (U : I → C)
      (f : ∀ i, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X →
        ∃ (K : Type (max u v)) (_ : Finite K) (V : K → C) (g : ∀ k, V k ⟶ X)
          (r : K → I),
          Presieve.ofArrows V g ∈ J X ∧
            ∀ k, ∃ (q : V k ⟶ U (r k)), q ≫ f (r k) = g k) :
    ∃ (ι : Type (max u w))
      (p : ι → GeometricMorphism (Type (max u w))
        (Sheaf J.toGrothendieck (Type (max u w)))),
      ∀ {F G : Sheaf J.toGrothendieck (Type (max u w))} (a : F ⟶ G),
        (∀ i, Function.Bijective ((p i).inverse.map a)) → IsIso a := by
  sorry

end CategoryTheory
