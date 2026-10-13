/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange

/-! # A finitely presented locus for one universal direct-image rank condition

Source: Stacks Project, Tags 0BDP, 0B91 and 0BDL, with the homogeneous-fibre
rank decomposition of the parent construction instead of connected fibres.
(blueprint: lem-sc-picard-universal-single-rank-locus-lfp).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Represent one ordinary direct-image rank condition without assuming connected fibres.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tags 0B91 and 0BDL.
The homogeneous-fibre and empty-fibre decomposition is the adaptation in the parent node.
(blueprint: lem-sc-picard-universal-single-rank-locus-lfp)

Proof: The rank-r locus X_r of E and its complement are clopen in X. Their images
are clopen in S because f is proper, flat and locally finitely presented. Let V=f(X).
The disjoint clopen subsets S_r=V minus f(X minus X_r) consist of nonempty fibres
having only rank r. A fibre with two different ranks has an open neighbourhood
in the intersection of the images of these rank loci, disjoint from every S_r.
The complement of V is the clopen empty-fibre component. A map satisfying the
single-image condition lands in the union of these components: test its condition
after the residue-field base change at each point; faithful field extension cannot
remove two different ranks on a fibre. Conversely this is the only restriction
imposed by the reference bundle clause.

On S_r the finite locally free F is finitely presented and relatively flat.
Tag 0B91 gives a perfect Rf_*F and arbitrary derived base change. All its derived
pullbacks have no negative cohomology, so locally its Tor amplitude is [0,b].
Apply Tag 0BDL in degree zero and rank r on such charts. Derived base change and
H^0 identify its condition with universal rank-r freeness of the ordinary direct
image. Every local rank witness equals r on a nonempty fibre, by invariant basis
number at a stalk of E. Fixed-rank freeness is local, so these witnesses are
exactly the single-image condition. This includes all nonreduced test schemes.

The chart immersions agree uniquely on overlaps by their universal property;
being monomorphisms, their identifications satisfy the cocycle condition and glue.
They are locally finitely presented by Tag 0BDL. Glue over the disjoint S_r, and
include the empty-fibre component, where the direct image is zero and E has
vacuous rank zero. The union is an immersion locally on S: near a homogeneous
fibre it is the corresponding immersion, and near a mixed fibre it is empty.
Local finite presentation is local on S. Factors of any test map exist locally
exactly under the single-image condition and glue uniquely. Empty test schemes
satisfy both sides; rank zero on nonempty fibres uses the same rank-zero locus.
-/
theorem exists_picardUniversalSingleRankLocus_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ LocallyOfFinitePresentation j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalSingleRankMatch f E F g := by sorry

end AlgebraicGeometry.Scheme
