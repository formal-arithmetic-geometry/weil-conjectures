/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.MaximumHistoryChronology

/-! # Lower-cut indexing of a supplied finite maximum history

Source: ILO VIII 2.1.1--2.1.4, 2.3.4--2.3.5, pp. 86--87, 91--92;
Step 5 of (blueprint: lem-trf-maximum-history-lower-cut-tower).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- The lower-cut diagrams and retained ideals for an already supplied chronology.
Source: ILO VIII 2.3.4--2.3.5 (blueprint: lem-trf-maximum-history-lower-cut-tower). -/
structure MaximumHistoryCutTower {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {r : ℕ}
    (S : MaximumHistoryChronology ν A r) where
  tower : LabeledEmbeddedResolutionTower (OrderDual {v : V // v ≠ ⊥}) A
  activeLabels : ∀ l, l ∈ tower.labels ↔ ∃ i, S.label i = l
  cutIndex : LowerSet (OrderDual {v : V // v ≠ ⊥}) →o Fin (r + 1)
  cutCount : ∀ D, (cutIndex D).val = Set.ncard {i : Fin r | S.label i ∈ D}
  cutFirst : cutIndex ⊥ = 0
  cutLast : cutIndex ⊤ = Fin.last r
  cutBefore : ∀ i, cutIndex (LowerSet.Iio (S.label i)) = i.castSucc
  cutAfter : ∀ i, cutIndex (LowerSet.Iic (S.label i)) = i.succ
  ambient : tower.ambient ≅ cutIndex.toFunctor.op ⋙ (S.history (Fin.last r)).ambient
  intrinsic : tower.intrinsic ≅ cutIndex.toFunctor.op ⋙ (S.history (Fin.last r)).intrinsic
  inclusion : tower.inclusion ≫ ambient.hom =
    intrinsic.hom ≫ Functor.whiskerLeft cutIndex.toFunctor.op (S.history (Fin.last r)).inclusion
  initialAmbient : (ambient.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun i ↦ (S.history (Fin.last r)).ambient.obj (op i)) cutFirst) ≫
      (S.history (Fin.last r)).initialAmbient.hom = tower.initialAmbient.hom
  initialIntrinsic : (intrinsic.app (op ⊥)).hom ≫
    eqToHom (congrArg (fun i ↦ (S.history (Fin.last r)).intrinsic.obj (op i)) cutFirst) ≫
      (S.history (Fin.last r)).initialIntrinsic.hom = tower.initialIntrinsic.hom
  ambientCenters : ∀ i, tower.center (S.label i) =
    ((S.history (Fin.last r)).center i).comap
      ((ambient.app (op (LowerSet.Iio (S.label i)))).hom ≫
        eqToHom (congrArg (fun j ↦ (S.history (Fin.last r)).ambient.obj (op j)) (cutBefore i)))
  intrinsicCenters : ∀ i, (tower.centerToIntrinsic (S.label i)).ker =
    ((S.history (Fin.last r)).centerToIntrinsic i).ker.comap
      ((intrinsic.app (op (LowerSet.Iio (S.label i)))).hom ≫
        eqToHom (congrArg (fun j ↦ (S.history (Fin.last r)).intrinsic.obj (op j)) (cutBefore i)))
  inactiveAmbient : ∀ l, l ∉ tower.labels →
    cutIndex (LowerSet.Iio l) = cutIndex (LowerSet.Iic l)

/-- Every supplied stopped chronology extends to all lower cuts, retaining its centers.
Source: ILO VIII 2.1.1--2.1.4 and 2.3.4--2.3.5, pp. 86--87, 91--92
(blueprint: lem-trf-maximum-history-lower-cut-tower).

Proof: for a lower set D count the indices whose strictly increasing label belongs to D.
The indices form the prefix of exactly that cardinality: if j is counted and i < j,
strict increase and lower closure count i as well. This defines the monotone index map
into Fin (r+1), with bottom, top, and the two principal cuts at label i sent respectively
to 0, r, i, and i+1. Compose the final history diagrams with its opposite functor. The
successive prefix identifications are obtained by composing the Extension isomorphisms;
their center equations identify each chronological ideal in the final history.
Use these isomorphisms to transport the recorded centers, blowups and scheme-theoretic
strict transforms at active labels. Their coherence, regularity and nowhere density
transport along isomorphisms. At an inactive label the index is constant; use the unit
ideal, its empty closed subscheme and the unique map to the intrinsic scheme. The unit
ideal and the corresponding intrinsic kernel are coherent. The ambient and intrinsic
transition maps are identities. The invertible-center blowup theorem identifies the
ambient transition with the ordinary unit-ideal blowup; its strict transform is the
original intrinsic scheme, since the complementary open is the whole ambient scheme.
Intervals containing no active labels likewise have constant index, so their maps are
isomorphisms. The final transform is regular. If an earlier cut is regular, its index
cannot be less than r by the chronology's nonregularity and prefix isomorphisms; hence
that cut contains every active label. Empty and regular input clauses follow from the
length-zero clauses of the chronology. All initial normalizations and ideal equations
follow from the chosen prefix identifications; no active intrinsic identity blowup is
deleted. This construction uses an existing finite chronology, not termination. -/
theorem maximumHistoryChronology_lowerCutTower {V : Type w} [LinearOrder V] [OrderBot V]
    {ν : ResolutionInvariantCalculus.{u} V} {A : EmbeddedResolutionPair.{u}} {r : ℕ}
    (S : MaximumHistoryChronology ν A r) : Nonempty (MaximumHistoryCutTower S) := by
  sorry

end AlgebraicGeometry
