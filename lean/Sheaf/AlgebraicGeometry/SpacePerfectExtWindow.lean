/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated

import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.AlgebraicGeometry.SpacePerfectUniformTor
import Sheaf.AlgebraicGeometry.AlgebraicSpaceGlobalSectionsAmplitude
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses

/-! # A finite cohomology window for Hom from a perfect algebraic-space complex

Source: Stacks Project, spaces-perfect.tex, Tag 09MB,
lemma-ext-from-perfect-into-bounded-QCoh, assertion (1)
(blueprint: lem-sfb-space-perfect-ext-window).

The existing small affine ringed model is equivalent to the small étale module topos.
Its derived category and quasi-coherent full subcategory retain the original module
universe and an arbitrary localization morphism universe.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Hom from a perfect complex vanishes whenever the target has quasi-coherent
cohomology and its cohomology sheaves vanish throughout a fixed finite interval.
The interval depends on X and P, and is independent of the target F.

Source: Stacks Project, spaces-perfect.tex, Tag 09MB,
lemma-ext-from-perfect-into-bounded-QCoh, assertion (1)
(blueprint: lem-sfb-space-perfect-ext-window).

Proof:
1. By lem-sfb-ringed-site-perfect-duality, D = RHom(P,O_X) is perfect. By
   lem-sfb-space-perfect-uniform-tor, D has quasi-coherent cohomology and Tor
   amplitude in an interval [s,t]. Choose N ≥ 0 from
   lem-sfb-space-global-sections-amplitude, and set a = -N-t and b = -s.
   Then a ≤ b, independently of F.
2. For F with zero cohomology on [a,b], use lem-sf-derived-truncation-triangle
   to form A → F → B → A[1], with A = tau_{≤a-1}F and B = tau_{≥a}F.
   The cohomology long exact sequence shows that A has cohomology only below a
   and B only above b. Both still have quasi-coherent cohomology.
3. The module category has closed additive symmetric tensor by
   lem-pc-sheaf-modules-tensor-closed, is Grothendieck abelian by
   lem-pur-ringed-site-grothendieck-abelian, and has functorial flat resolutions
   by lem-trf-site-functorial-flat-resolution. Apply
   lem-sc-source-tor-amplitude-upper-tensor-bound and
   lem-sc-source-tor-amplitude-lower-tensor-bound: D tensor^L A has no
   cohomology above -N-1 and D tensor^L B has none below 1. By
   lem-sfb-space-derived-qcoh-pullback-tensor both tensors remain quasi-coherent.
4. Tensor preserves the triangle by lem-sc-source-kflat-tensor-left-triangulated,
   using a K-flat representative from lem-weil-pbc-site-derived-tensor-descent.
   Apply RΓ, which is triangulated by lem-pc-right-derived-functor-triangulated.
   Lemma lem-sfb-space-global-sections-amplitude makes the first term vanish
   above -1 and the third below 1. The degree-zero long exact sequence gives
   H^0 RΓ(D tensor^L F) = 0.
5. The evaluation isomorphism of lem-sfb-ringed-site-perfect-duality identifies
   D tensor^L F with RHom(P,F). Lemma lem-pur-rhom-global-sections identifies
   its zeroth hypercohomology with Hom(P,F). Thus every such morphism is zero.

The small affine basis equivalence preserves cohomology, local finite-free-retract
models, and Hom, so this is the assertion on the original small étale ringed site. -/
theorem perfect_ext_window
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : X.IsAbsolutelyQuasiSeparated)
    [HasDerivedCategory.{w} X.SmallModules]
    (P : X.DerivedModules)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf P) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ F : X.DerivedQCoh,
      (∀ q : ℤ, a ≤ q → q ≤ b →
        IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj F.obj)) →
      Subsingleton (P ⟶ F.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
