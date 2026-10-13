/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Constructible

/-! # Retrocompactness of a fixed-rank Picard point locus

Source: Stacks Project, Tags 0BDP and 0BDI, rank decomposition and jump loci.
(blueprint: lem-sc-picard-universal-rank-match-fixed-rank-retrocompact).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Fixing the rank on the fibre makes the universal rank-matching point locus
retrocompact. This concerns points of S and does not assume a representing immersion.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, and Tag 0BDI.
(blueprint: lem-sc-picard-universal-rank-match-fixed-rank-retrocompact).

Proof:
1. Work over an affine open U of S. Its inverse image is quasi-compact. A finite
   trivializing cover of E gives finitely many rank loci there. Each is open and closed.
   A proper flat finitely presented morphism is both closed and open, so their images
   are open and closed in U. The locus where the nonempty fibre has constant rank r
   is therefore open and closed in U. The empty-fibre locus is also open and closed.
2. Proper flat perfect direct image and arbitrary base change identify the ordinary
   direct images on residue fields with degree-zero fibres of the perfect complexes
   Rf_*E and Rf_*(E dual). Tag 0BDI makes their dimension-r level sets locally
   constructible. Intersect them with the nonempty constant-r fibre locus from step 1.
3. On Spec kappa(s), these dimension conditions are equivalent to the universal rank
   condition: every further base change computes the same perfect complexes; near
   each point choose a finite-free model with no negative terms and degree-zero term
   of rank r. Over the field its outgoing matrix is zero, and remains zero on every
   scheme over that field. Thus both degree-zero direct images are locally free of
   rank r after every such base change. Conversely, testing the identity in the
   universal condition gives those dimensions, and the nonempty fibre fixes r.
4. The empty-fibre locus satisfies the universal condition (both direct images have
   rank zero); E on the empty fibre has every rank. Adjoin this clopen locus for every
   r, including positive r. The resulting set is locally constructible on U, hence
   constructible because U is affine and quasi-compact. A constructible subset of an
   affine scheme is quasi-compact: it is a finite union of differences of compact
   opens, each a closed subset of a compact open. Thus its intersection with U is
   compact. Any compact open of S is a finite union of affine opens, so the same
   finite-union argument proves the asserted retrocompactness. -/
theorem picardUniversalRankMatch_fixedRank_retrocompact {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    IsRetrocompact {s : S | PicardUniversalRankMatch f E (S.fromSpecResidueField s) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} := by sorry

end AlgebraicGeometry.Scheme
