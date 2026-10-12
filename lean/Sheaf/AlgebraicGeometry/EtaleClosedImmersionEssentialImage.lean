/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import Mathlib.CategoryTheory.EssentialImage
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Stalk

/-!
# Direct image along a closed immersion on abelian etale sheaves

Source: Stacks Project, Proposition 59.46.4 (Tag 04CA); blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-04ca.md` (blueprint: lem-kun-04ca).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Direct image along a closed immersion is fully faithful, inverse image is a left inverse,
and its essential image consists exactly of the abelian etale sheaves supported in the image
of the immersion. Source: Stacks Project, Proposition 59.46.4 (Tag 04CA)
(blueprint: lem-kun-04ca).

Proof: `def-weil-pbc-direct-image` gives `(i_*G)(V) = G(V ×_X Z)`.
By `prop-openclosed-lowerstar-fully-faithful`, the adjunction counit is an isomorphism,
so `i^{-1}i_*` is naturally isomorphic to the identity and `i_*` is fully faithful.
For a geometric point outside `Z`, pointed etale neighbourhoods factoring through `X \\ Z`
are cofinal: intersect each neighbourhood with this open complement. Their base changes to
`Z` are empty, where an abelian sheaf has zero sections. Thus every geometric stalk of
`i_*G` outside `Z` vanishes (`def-weil-pbc-geometric-stalks`), and this remains true for
any sheaf isomorphic to `i_*G`.
Conversely, for `F` supported in `Z`, consider the unit `F → i_*i^{-1}F`. At a geometric
point over `Z`, `lem-weil-pbc-inverse-image-stalk-germ` and
`lemma-openclosed-stalk-lowerstar` identify its map on stalks with the identity. Outside
`Z`, both stalks are zero, by the hypothesis and the preceding calculation. Hence the unit
is an isomorphism by `lemma-weil-pbc-geometric-stalk-conservative`, giving the essential-image
claim. The condition on support uses exactly `def-kun-support`: some nonzero geometric stalk
at a point is forbidden outside `Set.range i.base`. -/
theorem lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (lowerStar AddCommGrpCat.{u + 1} i).Full ∧
      (lowerStar AddCommGrpCat.{u + 1} i).Faithful ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} i ⋙ upperStar AddCommGrpCat.{u + 1} i ≅
        𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})) ∧
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        (lowerStar AddCommGrpCat.{u + 1} i).essImage F ↔
          Scheme.etaleSheafSupport F ⊆ Set.range i.base := by
  sorry

end AlgebraicGeometry.Etale
