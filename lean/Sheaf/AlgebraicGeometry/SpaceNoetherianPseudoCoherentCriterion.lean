/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion

/-! # The Noetherian pseudo-coherence criterion for algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 08IK, final equivalence;
sites-cohomology.tex, Tags 08FT and 08FU; spaces-cohomology.tex, Tag 07UB
(blueprint: lem-sfb-space-noetherian-pseudocoherent-criterion).

We use the existing fixed-degree strictly-perfect approximation predicate for every
integer. Cohomology is transported to the original module topos by the specified
small-model equivalence. On a locally Noetherian space, finite presentation is exactly
coherence (07UB), equivalently finite modules on all affine etale charts.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- On a Noetherian algebraic space, pseudo-coherence is equivalent to coherent
cohomology with a single global upper bound. No lower bound is imposed.
Source: Stacks Project, Tag 08IK, final equivalence; Tags 08FT, 08FU and 07UB
(blueprint: lem-sfb-space-noetherian-pseudocoherent-criterion).

Proof:
1. Restriction to an etale chart is localization of the small etale site and is exact:
   kernels restrict sectionwise, and local lifts for epimorphisms remain local lifts
   on the slice. Cohomology and quasi-coherence therefore restrict. Approximation
   conditions descend by composing covers, and zero sheaves are detected by an atlas.
2. On any affine chart U = Spec A, local Noetherianity makes A Noetherian, by
   pqf-lem-affine-open-locnoeth. Apply lem-sfb-affine-etale-derived-module-realization
   to obtain M in D(A) representing the restriction of K. Its cohomology comparison
   and sections comparison identify coherent cohomology with finite A-modules,
   in both directions, on every affine chart.
3. Use lem-sfb-etale-pseudocoherence-descent to pass the strictly-perfect
   approximation condition to the associated Zariski complex. The scheme definition
   def-pur-pseudo-coherent-complex and lem-pc-affine-pseudo-coherent-criterion identify
   this with a bounded-above finite-free representative of M, namely the predicate
   def-pc-ring-pseudo-coherent-complex. Tags 08FT and 08FU allow arbitrary
   representatives and replace derived approximation maps by chain maps locally.
4. In the forward direction apply
   lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion on every affine chart.
   Its finite cohomology modules give coherence of every cohomology sheaf (07UB).
5. Quasi-compactness gives a single surjective affine etale atlas by
   lem-sfb-qc-space-affine-etale-atlas. Apply the same ring criterion there to get
   one upper bound b; exact restriction and atlas detection give the global bound.
   For the empty space all module sheaves are zero and any integer is a bound.
6. Conversely, coherence and the global upper bound give finite bounded-above
   cohomology on every affine chart by step 2. The ring criterion and step 3 give
   pseudo-coherence on each chart. For each integer m, cover every site object by
   affine opens and compose their approximation covers. Step 1 descends this to
   the required m-approximation condition on every site object. -/
theorem isMPseudoCoherent_forall_iff_coherent_boundedAbove
    {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [HasDerivedCategory.{w} Y.SmallModules]
    (hqc : CompactSpace (Point Y.obj.obj)) (hqs : Y.IsAbsolutelyQuasiSeparated)
    (hln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (K : Y.DerivedModules) (hK : Y.derivedQCohProperty K) :
    (∀ m : ℤ, Y.IsMPseudoCoherent m K) ↔
      (∀ i : ℤ, SheafOfModules.IsFinitePresentation
        (Y.smallModuleEquivalence.inverse.obj
          ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K))) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor Y.SmallModules i).obj K) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
