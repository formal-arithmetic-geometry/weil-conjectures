/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData

/-! # Overlap isomorphisms on a normal tower level

Source: ILO IX 2.1 and Stacks Tags 0BQM and 033M (blueprint: lem-sfb-normal-tower-overlap-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open NormalTowerCoverGluing

/-- Local covers on charts of a single normal Noetherian scheme have unique compatible
overlap isomorphisms when their identifications agree on an open containing all generic points.
No finite subcover, common tower level, or global cover is asserted here.

Source: ILO IX Proposition 2.1, printed pp.133--134, extension of graphs;
Stacks Tag 0BQM, full faithfulness of restriction to a generic point, and Tag 033M.
(blueprint: lem-sfb-normal-tower-overlap-system)

Proof: Decompose A.left into its finitely many clopen normal integral components.
On any nonempty open part T of one component, its generic point belongs to the
inverse image of U. Restrict the two finite etale covers and the specified local
identifications to T. The composite of the first identification with the inverse
of the second defines a generic isomorphism. Extend its two directions using
finiteEtale_normalIntegral_generic_hom_full over T. Uniqueness shows that the
extensions are inverse, and that their restriction to T intersected with U is
the specified composite: apply generic faithfulness on that nonempty integral
open. Glue over the disjoint components of each pairwise overlap. The same
faithfulness proves uniqueness of this extension. On diagonal and triple overlaps,
the identity and cocycle equations hold over U by cancellation of the local
identifications, hence everywhere by generic faithfulness on each component.
All pullback comparisons are the canonical ones in localIdentification and
restrictLocalIso. Empty components or overlaps require only their unique maps;
if the inverse image of U is empty, generic containment forces A.left to be empty. -/
theorem normalTower_overlap_system {V : Scheme.{u}} (A : Over V) (U : V.Opens)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    {s : ℕ} (B : Fin s → Over V) (W : Fin s → V.Opens)
    (q : ∀ j : Fin s, A ⟶ B j)
    (Y : ∀ j : Fin s,
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart (B j) (W j)))
    (θlocal : ∀ j : Fin s,
      (MorphismProperty.Over.pullback _ ⊤
        (chartInclusion (B j) (inf_le_left : W j ⊓ U ≤ W j))).obj (Y j) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen (B j) (inf_le_right : W j ⊓ U ≤ U))).obj P)
    [IsLocallyNoetherian A.left] [CompactSpace A.left]
    (hNormal : ∀ x : A.left, IsDomain (A.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (A.left.presheaf.stalk x))
    (hGeneric : ∀ C : Set A.left, C ∈ irreducibleComponents A.left →
      ∀ η : A.left, IsGenericPoint η C → A.hom η ∈ U) :
    Nonempty (Overlaps A U P B W q Y θlocal) := by sorry

end AlgebraicGeometry.Scheme
