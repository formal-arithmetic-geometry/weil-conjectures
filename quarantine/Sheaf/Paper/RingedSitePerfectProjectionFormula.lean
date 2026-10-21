/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.RingedExchangeTensorCoherence
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.ElementRestrictionHom
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Perfect projection formula on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tag 0944, lemma-projection-formula and
its preceding projection morphism (blueprint: lem-sbc-ringed-site-perfect-projection-formula).
-/

@[expose] public section

universe u w

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The canonical counit projection mate is invertible for every locally perfect coefficient.
The corners and edge are the recorded small-site presentation of the ringed topoi, their
ordinary unbounded derived module categories, and derived adjunction. The tensor models
identify their tensor bifunctors with direct-sum total tensor on flat K-flat representatives.
Perfectness uses covering sieves and bounded degreewise finite-free retracts, with bounds
and ranks allowed to vary over the covering objects. The source object is unbounded.

Source: Stacks Project, Cohomology on Sites, Tag 0944, lemma-projection-formula;
the projection morphism immediately preceding it
(blueprint: lem-sbc-ringed-site-perfect-projection-formula).

Proof:
1. By `lem-weil-pbc-ringed-projection-mate-exact`, tensor with the direct image and
   direct image after tensor with derived pullback are exact additive functors. Their
   counit mate is natural and compatible with all integer shifts and distinguished
   triangles. Its value at the ring is the identity under the unit identifications,
   so its value at every integer shift of the ring is invertible.
2. Additivity gives finite sums, including rank zero. Naturality gives stability under
   retracts: for i : Q -> H and p : H -> Q with i followed by p equal to identity,
   the inverse is G(i), followed by the inverse at H, followed by F(p). Thus every
   shift of a finite-free summand belongs to the isomorphism locus.
3. For a bounded strict-perfect representative, its successive stupid tails form
   degreewise split short exact sequences. By
   `lem-weil-pbc-degreewise-split-derived-triangle` these give distinguished triangles.
   Descending induction from the zero tail and `lem-sf-triangle-morphism-iso` give
   invertibility for the representative, then for every derived object isomorphic to it.
   The degreewise splittings need not be maps of complexes into a fixed free complex.
4. On a cover where the coefficient has such a representative, use
   `lem-weil-pbc-element-restriction-hom` to identify ordinary localized sites with
   element-site slices. The comparison of
   `lem-sbc-ringed-topos-sheaf-slice-derived-comparison` identifies the slice adjunctions
   and gives invertible exchange. Canonical restriction tensor comparisons from
   `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, together with
   `lem-weil-pbc-ringed-exchange-tensor-coherence`, identify restriction of this precise
   counit mate with the slice projection mate. Step 3 proves its invertibility there.
   Each cover member uses its own bounds and ranks.
5. By `lem-weil-pbc-exact-functor-complex-cohomology`, exact restriction commutes with
   every cohomology functor, naturally also on roofs representing derived arrows.
   The domains of these covers over all site objects form a small covering family.
   Apply `lem-sfb-sheaf-cover-local-isomorphism` to each cohomology map; its inverse
   is module-linear since the map is linear and invertible. Finally
   `lem-weil-pbc-unbounded-derived-iso-cohomology` makes the derived mate invertible.
   No common bound on the representatives or on the source object is used. -/
theorem ringedSitePerfectProjectionFormula
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (E : X.mateDerived) (P : Y.mateDerived)
    (hP : IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} Y.ring P) :
    IsIso (e.projection a b E P) := by
  sorry

end SheafOfModules
