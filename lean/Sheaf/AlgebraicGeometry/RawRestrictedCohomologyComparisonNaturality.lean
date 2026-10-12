/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Pullback compatibility of restricted derived-Hom evaluation

Source: Stacks Project, Tags 03Q8, 0BKV and 0EZM.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-naturality).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit evaluation map commutes with the explicit raw pullback.
This asserts compatibility of a constructed map, independently of invertibility.
Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tags 0BKV and 0EZM.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-naturality).

Proof: Write V = U times_S Y, V' = U times_S Y', r : V -> Y,
r' : V' -> Y' and q : V' -> V. The pullback projection identities give
r' followed by a = q followed by r. Naturality of the sheafification unit and
of the inverse-image adjunction unit identifies the pullback of the represented
identity section on V with the represented identity section on V'. The
inverse-image composition isomorphisms transport the coefficient restriction
along this equality by exactly rawAffineRestrictedCoefficient. Apply restricted
derived sections to the five factors defining abelianHigherDirectImageRawPullback.
Naturality of mapDerivedCategorySingleFunctor and mapDerivedCategoryFactors
moves the single-complex comparisons to the ends. Naturality of the derived
inverse-image/direct-image adjunction unit, with the triangle identities,
identifies the intervening map on derived sections with the unit followed by
the derived global-sections composition comparison; this is the derived map
whose homology defines rawAffineComplexPullback. The shift comparisons commute
with these maps, so zeroth homology on the shifted object becomes p-th homology
on the unshifted restricted single complex. Evaluate the resulting commuting
square at the represented identity generator. The left composite is the
restricted cohomology map after evaluation, and the right composite is evaluation
after the raw pullback. These are the two sides of the stated equality.
This calculation involves no inverse to the evaluation map and works also in
degree zero and when either restricted scheme is empty. -/
theorem rawRestrictedCohomologyComparison_naturality {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    rawAffineRestrictedCohomologyMap a h h' w p F F' φ U
        (rawRestrictedCohomologyComparison h p F U t) =
      rawRestrictedCohomologyComparison h' p F' U
        (abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) := by sorry

end AlgebraicGeometry.Etale
