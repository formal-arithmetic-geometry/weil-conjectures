/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal

import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import Sheaf.CategoryTheory.Sites.UnboundedLeraySections
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # A uniform upper bound for derived pushforward on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 08FA,
lemma-quasi-coherence-direct-image (2), shifted using Tag 08F7 (3)
(blueprint: lem-sfb-space-derived-pushforward-upper-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Uniform upper cohomological dimension on all quasi-coherent derived objects,
including those unbounded below.
Source: Stacks Project, Tag 08FA, lemma-quasi-coherence-direct-image (2), shifted
by the upper endpoint in Tag 08F7 (3)
(blueprint: lem-sfb-space-derived-pushforward-upper-bound).

Proof:
1. Choose N >= 1 by lem-sfb-space-affine-chart-uniform-qcoh-vanishing. On every
   affine etale V over Y, evaluation on X times_Y V after enlarged-site extension
   is left exact and preserves countable products: kernels and products of module
   sheaves are sectionwise, and extension is an equivalence.
2. Apply lem-sfb-space-product-preserving-derived-functor-upper-bound to this
   evaluation functor. Its derived value on E vanishes in every degree m >= b + N;
   its input is the quasi-coherent cohomology of E, without a lower bound on E.
3. By lem-trf-space-enlarged-etale-ringed-site-model and
   lem-trf-space-chart-limit-enlarged-sections, the enlarged-site direct image is
   the canonical compatible-chart direct image. Apply
   lem-sfb-ringed-site-unbounded-leray-sections to identify its derived sections
   over V with the derived evaluation in step 2. Extension equivalences preserve
   acyclic complexes and homotopies, hence K-injectives. Choose a K-injective
   representative J of Rf_*E by prop-pur-kinjective-resolutions-exist.
4. On every affine etale V, J(V) computes these derived sections, so every
   degree-m cycle is a boundary. All etale scheme charts have affine open covers.
   Since kernels are sectionwise and cokernels are sheafified sectionwise
   cokernels, the cohomology sheaf in degree m is zero. -/
theorem derivedDirectImage_uniform_upper_bound
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom))
    (hY : CompactSpace (Point Y.obj.obj)) :
    ∃ N : ℤ, 1 ≤ N ∧ ∀ (b : ℤ) (E : X.DerivedModules),
      X.derivedQCohProperty E →
      (∀ q : ℤ, b < q → IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj E)) →
      ∀ m : ℤ, b + N ≤ m →
        IsZero ((DerivedCategory.homologyFunctor Y.SmallModules m).obj
          ((derivedDirectImage f).obj E)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
