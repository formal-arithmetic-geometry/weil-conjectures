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
import Sheaf.AlgebraicGeometry.PicardFiberRankClopen
import Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible
import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion
import Sheaf.Topology.ConstructibleIsRetrocompact

/-! # Retrocompactness of a fixed-rank Picard point locus

Source: Stacks Project, Tags 0BDP and 0BDI, rank decomposition and jump loci.
(blueprint: lem-sc-picard-universal-rank-match-fixed-rank-retrocompact).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem locallyConstructible_isRetrocompact (S : Scheme.{u})
    (Z : Set S) (hZ : Topology.IsLocallyConstructible Z) : IsRetrocompact Z := by
  intro U hUc hUo
  have hcompact (V : S.affineOpens) : IsCompact (Z ∩ (V.1 : Set S)) := by
    have : IsAffine V.1.toScheme := V.2
    have hc := (hZ.preimage_of_isOpenEmbedding V.1.ι.isOpenEmbedding).isConstructible
    have hk := hc.isRetrocompact.isCompact
    have hi := hk.image V.1.ι.continuous
    simpa only [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
      using hi
  have hb : TopologicalSpace.IsTopologicalBasis
      (Set.range (fun V : S.affineOpens ↦ (V.1 : Set S))) := by
    simpa only [TopologicalSpace.Opens.IsBasis, Set.image_eq_range]
      using S.isBasis_affineOpens
  obtain ⟨T, hT, hUT⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb U hUc hUo
  rw [hUT]
  simp only [Set.inter_iUnion]
  exact hT.isCompact_biUnion fun V _ ↦ hcompact V

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
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} := by
  let A : Set S := {s | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r}
  let B : Set S := {s | IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u})}
  let C : Set S := {s | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r}
  let D : Set S := {s | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj
        (Modules.dual E))) r}
  obtain ⟨hB, hA⟩ := picardFiberRank_clopen f E r
  have hAlc : Topology.IsLocallyConstructible A :=
    IsRetrocompact.isLocallyConstructible hA.isOpen
      (show IsRetrocompact A from fun _ hUc _ ↦ hUc.inter_left hA.isClosed)
  have hBlc : Topology.IsLocallyConstructible B :=
    IsRetrocompact.isLocallyConstructible hB.isOpen
      (show IsRetrocompact B from fun _ hUc _ ↦ hUc.inter_left hB.isClosed)
  have hClc : Topology.IsLocallyConstructible C :=
    picardFiberDirectImageRank_locallyConstructible f E r
  have : (Modules.dual E).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual E
  have hDlc : Topology.IsLocallyConstructible D :=
    picardFiberDirectImageRank_locallyConstructible f (Modules.dual E) r
  have heq : {s : S | PicardUniversalRankMatch f E (S.fromSpecResidueField s) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} =
      A ∩ (B ∪ (C ∩ D)) := by
    ext s
    change (_ ∧ s ∈ A) ↔ (s ∈ A ∧ (s ∈ B ∨ (s ∈ C ∧ s ∈ D)))
    constructor
    · rintro ⟨hR, hEr⟩
      exact ⟨hEr, (picardUniversalRankMatch_residue_iff f E r s hEr).mp hR⟩
    · rintro ⟨hEr, h⟩
      exact ⟨(picardUniversalRankMatch_residue_iff f E r s hEr).mpr h, hEr⟩
  rw [heq]
  exact locallyConstructible_isRetrocompact S _ (hAlc.inter (hBlc.union (hClc.inter hDlc)))

end AlgebraicGeometry.Scheme
