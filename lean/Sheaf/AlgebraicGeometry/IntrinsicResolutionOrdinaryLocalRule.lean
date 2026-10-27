/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H9
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution
public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData
public import Sheaf.AlgebraicGeometry.LabeledOrdinaryResolutionDescentData

/-! # Ordinary local rules from intrinsic lower-cut resolution diagrams

Source: ILO VIII 2.1.4--2.1.9 and 2.3.4--2.3.5, pp.87--88,91--92.
This is a finite-index realization of the given intrinsic assignment, not an
existence theorem for resolution (blueprint: lem-trf-intrinsic-ordinary-local-rule).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

namespace AlgebraicGeometry

/-- Realize the specified intrinsic assignment as an ordinary local rule on the same
embeddable inputs. The tower equality fixes both the ordinary tower and its labels;
only the presentation of the comparison by finite indices changes.

Source: ILO VIII 2.1.4--2.1.9, 2.3.4--2.3.5, pp.87--88,91--92; the finite-cut
realization implicit in the intrinsic-to-descent assembly
(blueprint: lem-trf-intrinsic-ordinary-local-rule).

Proof:
The three descriptions of an embeddable input are equivalent. A permitted embedding
with an isomorphic source gives the closed immersion by composing with that isomorphism;
conversely a literal closed immersion gives an embedded pair with identity source model.
Use the ordinary tower and label embedding already in `I.tower` on each input. Proof
irrelevance makes the choice of witness immaterial. The coherent module condition on
each cut center transports along its stage isomorphism to the corresponding ordinary
center, using `center_ordinary`; the finite-type-with-finite-type-kernels criterion is
exactly coherence after identifying open restriction with the ringed-space slice.
Regularity is the supplied `resolves` field and empty triviality is `empty_input`.

For a smooth map use `I.comparison`. Its retained-label clause embeds the finite source
label list into the target list, uniquely, preserving order. At target level i take the
lower cut containing precisely the first i target labels: use the cut before label i,
and the top cut at the last level. Define count(i) to be the source index of this cut.
The index-label equivalence gives count(0)=0, count(last)=last, count before and after
each retained label, and equality of counts at every deleted label. Conjugate the cut
map by the two stage isomorphisms to define the finite level map. Cartesian squares
transport along these isomorphisms. Naturality of the cut map and of the stage
isomorphisms gives transition naturality. The cut center equality, `center_ordinary`
and functoriality of ideal comap give the retained ideal equality. The retained-label
criterion gives deletion exactly when the pulled-back ideal is unit. This constructs
all fields of `Comparison`, with its label equality, on the specified ordinary towers.
Zero-length towers use only the top/bottom cut and the unique map of singleton indices;
there are no center or survivor obligations in that case. -/
theorem intrinsicResolution_ordinary_localRule (L : Type w) [LinearOrder L]
    (E : SynchronizedEmbeddedResolution.{u, w} L)
    (I : IntrinsicResolutionOfEmbedded L E) :
    ∃ B : OrdinaryResolutionDescent.LocalRule.{u, w} L,
      (∀ (S : RationalResolutionInput.{u}) (eS : OrdinaryResolutionDescent.Embeddable S)
        (p : RationalResolutionEmbedding S),
        (⟨(B.tower S eS).tower, (B.tower S eS).labels⟩ :
          LabeledOrdinaryTower L S.scheme) =
        ⟨(I.tower ⟨S, ⟨p⟩⟩).ordinary, (I.tower ⟨S, ⟨p⟩⟩).label⟩) := by sorry

end AlgebraicGeometry
