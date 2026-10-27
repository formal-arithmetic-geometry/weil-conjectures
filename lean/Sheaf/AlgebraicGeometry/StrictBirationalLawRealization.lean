/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Sheaf.AlgebraicGeometry.StrictBirationalGroupLaw
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.InvariantOpenImagePullback
import WeilConjectures.AlgebraicGeometry.EffectiveDescent

/-!
# Realization of a strict birational group law

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 5.2 Theorem 3,
5.3 Lemmas 5--8, 6.5 Corollary 2, and 5.1 Proposition 3
(blueprint: lem-sfb-strict-birational-law-realization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A strict birational group law over a field or DVR has a smooth separated finite-type
realization, unique up to a unique group isomorphism that preserves its dense open chart.

Source: BLR, 5.2 Theorem 3, 5.3 Lemmas 5--8, 6.5 Corollary 2, 5.1 Proposition 3
(blueprint: lem-sfb-strict-birational-law-realization).

Proof:
1. Pass to a strict henselization B' of B. The triples construction
   (lem-weil-pbc-strict-henselization-triples) and faithful flatness
   (lem-sc-strict-henselization-faithfully-flat) give an affine fpqc cover.
   In the DVR case, lem-wf-geometric-triples-colimit-comparison and
   lem-sc-strict-henselization-dvr identify B' as a DVR; in the field case it is a
   separable closure. Thus B' is noetherian and normal. Base change preserves strictness
   by lem-sfb-strict-law-base-change.
2. Apply lem-sfb-strict-law-finite-translate-envelope over B' to enlarge the chart to
   Z', with the law defined on the full original square and an S'-section. Apply
   lem-sfb-strict-law-complete-square-group to obtain the smooth separated finite-type
   group H' and the dense open immersion of X'.
3. On the double overlap, the two copies of X' carry the same law. By
   lem-sfb-rational-group-hom-extension their identification extends uniquely to a group
   isomorphism between the two pullbacks of H'. Uniqueness on the triple overlap gives
   the cocycle of def-pd-descent-datum. These extension results permit arbitrary bases.
4. Apply lem-sfb-smooth-group-field-trait-descent to descend H'. The invariant chart
   descends to an open O in H by lem-trf-invariant-open-image-pullback. Descend X' ≅ O'
   and its inverse by lem-pd-morphisms-descend, obtaining X ≅ O and hence i : X → H.
5. Density of the image descends fibre by fibre: a nonempty open in H_s has nonempty
   pullback to any residue-field extension by lem-weil-pbc-surjective-base-change and
   therefore meets X'. Faithfulness in lem-pd-morphisms-descend descends the equality
   between multiplication and m on the strict chart domain.
6. For any two realizations, identify their dense open charts via X. The resulting
   birational map preserves multiplication. Apply lem-sfb-rational-group-hom-extension
   to it and its inverse. They give the unique group isomorphism restricting to this
   identification, and hence commuting with the two immersions on all of X. -/
theorem strictBirationalGroupLaw_realization
    (B : Type u) [CommRing B] [IsDomain B]
    (hB : IsField B ∨ IsDiscreteValuationRing B)
    (X : Over (Spec (CommRingCat.of B)))
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hne : ∀ s : Spec (CommRingCat.of B), Nonempty (X.hom.fiber s))
    (m : StrictBirationalGroupLaw X) :
    (∃ (H : Grp (Over (Spec (CommRingCat.of B)))) (i : X ⟶ H.X), m.Realizes H i) ∧
    (∀ (H₁ H₂ : Grp (Over (Spec (CommRingCat.of B))))
      (i₁ : X ⟶ H₁.X) (i₂ : X ⟶ H₂.X),
      m.Realizes H₁ i₁ → m.Realizes H₂ i₂ →
      ∃! a : H₁ ≅ H₂, i₁ ≫ a.hom.hom.hom = i₂) := by
  sorry

end AlgebraicGeometry
