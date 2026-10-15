/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion
import Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange
import Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality

/-!
# Bounded-below derived smooth base change

Source: blueprint, sec-smooth-base-change, sk-rem-rest, order 1440
(blueprint: sbc-thm-bounded-below-derived-smooth-base-change).

The conclusion includes membership of both images in the full allowable-torsion
subcategory as well as invertibility of the specified canonical exchange arrow.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Smooth base change in the bounded-below allowable-torsion category on X.
Source: blueprint, sec-smooth-base-change, sk-rem-rest, order 1440
(blueprint: sbc-thm-bounded-below-derived-smooth-base-change).

Proof:
1. Choose a lower cohomological bound a for K. For each integer n, the standard
truncation K_n = tau_le_n K is bounded, is zero for n < a, and has allowable-torsion
cohomology (sbc-def-derived-categories-with-allowable-torsion and
 def-sbc-standard-tstructure-derived-category).
2. Apply sbc-thm-bounded-allowable-torsion to K_n using smoothness and qcqs.
This gives the ambient isomorphism without an upper bound on its images.
3. The bounded-below truncation criterion identifies degree-n cohomology of both
images of K_n with those of K. Naturality gives a commutative square; conjugating
its top isomorphism by these vertical isomorphisms gives an isomorphism on H^n
(sbc-lem-bounded-below-truncation-criterion and sbc-lem-bc-naturality).
4. Derived direct images and exact inverse images preserve bounded-below objects.
Detection on cohomology stalks gives the ambient isomorphism
(def-weil-pbc-direct-image, def-weil-pbc-derived-inverse-image, and
lem-weil-pbc-derived-stalk-conservative).
5. An allowable-torsion sheaf F is the filtered union of its kernels F[m] for
positive m with prime factors in P. Exact stalks preserve these kernels and their
colimit, and detect that the union is F. Qcqs higher direct images commute with
this filtered colimit; R^p g_* F[m] is killed by m by additivity. Hence R^p g_* F
has allowable-torsion stalks (prop-weil-pbc-geometric-stalks-exact,
lem-weil-pbc-geometric-point-pullback-stalk, def-weil-pbc-inverse-image,
lemma-weil-pbc-geometric-stalk-conservative,
lemma-weil-pbc-direct-image-filtered-colimit, and def-weil-pbc-direct-image).
6. The first finite hypercohomology filtration has graded terms subquotients of
R^p g_* H^q(K), with a <= q <= n. Allowable torsion is stable under subgroups,
quotients and extensions: multiply annihilators in an extension. Induction along
the filtration proves allowable torsion of H^n(Rg_*K)
(def-weil-pbc-hypercohomology-filtrations and exact geometric stalks).
7. Exact inverse image commutes with cohomology. The stalk of f^{-1}H^n(Rg_*K)
at x is the stalk of H^n(Rg_*K) at f(x), by inverse-image composition and the
geometric-point stalk comparison. Thus the source image is allowable torsion;
the target is too by the ambient isomorphism. Both are bounded below by step 4.
The allowable-torsion category is full, so the arrow and its inverse belong to it
(prop-weil-pbc-inverse-image-exact, lem-weil-pbc-exact-functor-bounded-below,
lem-weil-pbc-geometric-point-pullback-stalk, lem-weil-pbc-inverse-image-composition,
and sbc-def-derived-categories-with-allowable-torsion). -/
theorem boundedBelow_derived_smooth_baseChange
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g)
    (K : AbelianDerivedCategoryPlusTorsionOfPrimes T S.invertiblePrimes) :
    allowableTorsionPlusProperty X S.invertiblePrimes
        (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) ∧
      allowableTorsionPlusProperty X S.invertiblePrimes
        (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)) ∧
      IsIso (abelianDerivedBaseChangeArrow sq K.obj) := by
  sorry

end AlgebraicGeometry.Etale
