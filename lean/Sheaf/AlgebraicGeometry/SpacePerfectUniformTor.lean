/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SplitPerfectDualTorWindow

/-! # A global Tor interval for a perfect complex on a quasi-compact algebraic space

Source: Stacks Project, spaces-perfect.tex, Tags 08JL and 09MB;
sites-cohomology.tex, Tags 08G8 and 08G1
(blueprint: lem-sfb-space-perfect-uniform-tor).

The existing small affine ringed model represents the small étale module topos in
its original section universe. Quasi-coherence is tested after the inverse of its
specified module restriction equivalence. The tensor is the recorded K-flat tensor.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A perfect object has quasi-coherent cohomology and a single finite Tor interval
on a quasi-compact algebraic space. The test modules range over the entire module
category, and the interval is independent of the test module.

Source: Stacks Project, spaces-perfect.tex, Tag 08JL, lemma-pseudo-coherent;
Tag 09MB, lemma-ext-from-perfect-into-bounded-QCoh, global Tor interval input;
sites-cohomology.tex, Tags 08G8 and 08G1
(blueprint: lem-sfb-space-perfect-uniform-tor).

Proof:
1. Choose an étale scheme atlas (def-trf-algebraic-space). Local perfectness
   (def-weil-pbc-strict-perfect-coefficient-package) refines it to a jointly
   surjective family U_lambda on which E has a bounded finite-free-retract model
   P_lambda, supported in [a_lambda,b_lambda]. Give a zero model the interval [0,0].
2. Finite free modules are quasi-coherent. A retract with maps i,p is the kernel
   of 1-i p, so lem-sfb-space-qcoh-kernels-colimits makes each model term and
   its cohomology quasi-coherent. The slice site at a scheme chart is its own
   small étale site, by lem-trf-space-chartwise-etale-permanence. Exact restriction
   (lem-weil-pbc-ringed-sheaf-slice-adjunction) commutes with cohomology. Pull back
   the local presentation covers using lem-trf-space-fibre-products-etale-covers
   and compose them; the local-presentation definition descends quasi-coherence.
3. By lem-a1-etale-scheme-map-open-image the chart images form an open cover.
   Quasi-compactness gives a finite subcover F. Take a to be the minimum of 0
   and its lower bounds and b the maximum of 0 and its upper bounds. Then a ≤ b
   and every chosen local interval lies in [a,b], including when F is empty.
4. For any module M and q outside [a,b], restrict to a selected chart. The sheaf
   Hom_X(-,U_lambda) is a sheaf because X and the representable chart are fppf
   sheaves (def-trf-algebraic-space, def-trf-scheme-algebraic-space, def-pc-fppf-site).
   Its element site is the slice. The slice adjunction identifies pullback with
   exact restriction. The canonical comparison of
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback identifies the restricted
   tensor with P_lambda tensor^L M|U_lambda. By lem-sfb-split-perfect-dual-tor-window
   its q-th cohomology is zero. Pullback covers from
   lem-trf-space-fibre-products-etale-covers and the uniqueness part of the sheaf
   axiom imply global vanishing. This includes the empty covering of the empty space.

The small affine basis equivalence preserves module sheaves, cohomology, local
finite-free-retract models, and K-flat derived tensor. Thus this is the same assertion
on the original small étale ringed site; no separation or rank bound is required. -/
theorem perfect_quasiCoherent_uniformTor
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj))
    (E : X.DerivedModules)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E) :
    X.derivedQCohProperty E ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (M : X.SmallModules) (i : ℤ), i < a ∨ b < i →
          IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj
            ((SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, u, u, w}
              X.smallEtaleModelTopology X.smallStructureSheaf).obj
                (E, (DerivedCategory.singleFunctor X.SmallModules 0).obj M))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
