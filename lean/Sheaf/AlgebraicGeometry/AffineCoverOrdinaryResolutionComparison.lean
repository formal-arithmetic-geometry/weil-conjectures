/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryResolutionDescentData

/-! # Gluing one smooth comparison of labeled ordinary resolution towers

Source: ILO, Travaux de Gabber, VIII 2.1.9 and 2.3.5(ii), pp.88,92.
-/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrdinaryResolutionDescent

/-- A single smooth map admits a labeled comparison agreeing with the prescribed
comparisons on all subordinate affine covers. No identity, composition, surjectivity,
chart normalization or empty-input assertion is included.
Source: ILO VIII 2.1.9 and Remark 2.3.5(ii)
(blueprint: lem-trf-affine-cover-ordinary-resolution-comparison).

Proof: Choose a finite affine cover of the target and a finite affine refinement
of its inverse image on the source. Their whole disjoint unions are embeddable;
the induced map is smooth by restriction and locality on the source. Apply the
specified local comparison and the uncontracted cover identifications. Their
length equalities transport the local ordered survivor embedding and count to
the global finite index sets. At each original level, use flat base change of
ordinary blowups to view the local maps as maps to the uncontracted pullback.
They agree on overlaps: refine the source overlap by affine opens mapping into
affine opens of the target overlap, use the datum's cocycle to identify the
extended ideals. The level-map uniqueness theorem
`smoothComparison_levelMap_unique` identifies the maps to the uncontracted
pullback level, since their composites to the base agree. Deleted unit stages are
identities. Glue these maps and their inverses.
The resulting level squares are cartesian, commute with all transitions and
identify the retained ideals. Unit ideals are detected on the covering, so the
deleted-stage equivalence also descends. Label preservation is the local label
equation transported by the cover identifications. For any other pair of covers,
repeat the overlap refinement; the cocycle and level-map uniqueness give
the same ideals and maps, hence the same survivor indices and counts. Gluing
uniqueness gives the stated restriction equations for every cover simultaneously.
Do not assume intersections of affine opens affine. The argument includes empty
covers and uses each disjoint union as one input, so stages remain synchronized. -/
theorem affineCover_ordinaryResolution_comparison
    {L : Type w} [LinearOrder L] (D : Datum.{u, w} L)
    (S T : RationalResolutionInput.{u}) (h : T.scheme ⟶ S.scheme)
    (over : h ≫ S.structureMap = T.structureMap) [Smooth h] :
    ∃ c : Comparison h (D.tower S) (D.tower T),
      ∀ (U : AffineCover S) (V : AffineCover T)
        (v : V.total.scheme ⟶ U.total.scheme) (_square : v ≫ U.map = V.map ≫ h)
        (overV : v ≫ U.total.structureMap = V.total.structureMap) [Smooth v],
        Nonempty (Restricts c U V (D.cover S U) (D.cover T V)
          (D.localRule.comparison U.total V.total U.embeddable V.embeddable v overV)) := by
  sorry

end AlgebraicGeometry.OrdinaryResolutionDescent
