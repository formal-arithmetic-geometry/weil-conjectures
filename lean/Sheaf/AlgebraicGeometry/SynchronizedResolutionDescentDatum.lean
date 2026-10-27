/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H9
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryZariskiResolutionData
public import Sheaf.AlgebraicGeometry.LabeledOrdinaryResolutionDescentData

/-! # Packaging a fixed synchronized Zariski resolution for smooth descent

Source: ILO VIII 2.3.4 and Remark 2.3.5(ii), pp.91--92.
The global towers and their synchronized descent are hypotheses; the conclusion supplies
only the affine-cover datum (blueprint: lem-trf-synchronized-resolution-descent-datum).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- The specified Zariski descent of the specified local smooth rule gives the datum for
smooth comparison descent. Both the local rule and every global labeled tower are fixed.
No global smooth comparisons, identity/composition laws or nondeletion are concluded.

Source: ILO VIII 2.3.4 and Remark 2.3.5(ii), pp.91--92, applied to the uncontracted
cover identifications and their uniqueness
(blueprint: lem-trf-synchronized-resolution-descent-datum).

Proof:
Give each global tower R(S) its regularity and coherent-center proofs from hR. For a
finite affine cover U in the smooth-descent interface, enumerate its finite index type
by Fin n. Replace each spectrum chart by its canonical isomorphic affine open in S.
Transport the component arrows and their coproduct universal property through these
isomorphisms. This gives `ResolutionAffineCover` with the very same total input and map;
no new total scheme is chosen. Its covering and rational structure equations follow
from U's covering and component equations. Apply hdescent to obtain the unique full
cartesian comparison with A on this total input. The given equality hAB transports it
to B on that input, preserving lengths, maps, ideals and labels; it is the required
`CoverIdentification`. Its underlying global tower is literally R(S).

For a smooth v between two such totals over S, label preservation in B.comparison and
the two full cover identifications imply equality of both total label ranges. Thus the
survivor order embedding is a bijection of the equal finite ordered lists. Its count
is the corresponding cast, so the count cocycle holds, including zero-length towers.
After this identification, composing the source cover comparison with B.comparison
is an uncontracted tower comparison to the target cover comparison over S, with the
same extended centers. The maps agree by induction on stages: at level zero the
cartesian square and initial isomorphisms fix the map; at the next ordinary blowup the
center is invertible on the source and the blowup universal property makes the lift
unique. The same argument treats an inserted unit stage, whose blowup is the identity.
This proves the map cocycle, with exactly the index transports of `Datum`. It is
independent of the enumeration because two enumerations induce the same canonical
cover maps. These constructions give the required datum, its fixed local rule and the
literal equality of the global labeled towers. -/
theorem synchronizedResolution_descentDatum (L : Type w) [LinearOrder L]
    (A : OrdinaryZariskiResolutionRule.{u, w} L)
    (B : OrdinaryResolutionDescent.LocalRule.{u, w} L)
    (hAB : ∀ (S : RationalResolutionInput.{u}) (eA : S.IsEmbeddable)
      (eB : OrdinaryResolutionDescent.Embeddable S),
      A.tower S eA = ⟨(B.tower S eB).tower, (B.tower S eB).labels⟩)
    (R : ∀ S : RationalResolutionInput.{u}, LabeledOrdinaryTower L S.scheme)
    (hR : ∀ S, (R S).IsResolution)
    (hdescent : ∀ S, A.IsSynchronizedDescent S (R S)) :
    ∃ D : OrdinaryResolutionDescent.Datum.{u, w} L,
      D.localRule = B ∧
      ∀ S, (⟨(D.tower S).tower, (D.tower S).labels⟩ :
        LabeledOrdinaryTower L S.scheme) = R S := by sorry

end AlgebraicGeometry
