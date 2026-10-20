/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

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
  classical
  let A := AddCommGrpCat.{u + 1}
  let W : X.Opens := ⟨(Set.range i.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have hji := disjoint_range_of_range_eq_compl W.ι i hij
  refine ⟨inferInstance, inferInstance,
    ⟨asIso (upperStarLowerStarAdjunction A i).counit⟩, fun F ↦ ?_⟩
  -- Support in the closed image means that restriction to its open complement is zero.
  have hsupport : Scheme.etaleSheafSupport F ⊆ Set.range i.base ↔
      CategoryTheory.Limits.IsZero ((upperStar A W.ι).obj F) := by
    constructor
    · intro hF
      apply ((Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale W A).isZero_iff).2
      rintro ⟨_, ⟨w⟩⟩
      have hz : CategoryTheory.Limits.IsZero
          ((Scheme.pointSmallEtale (W.toScheme.algClosurePoint w ≫ W.ι)).sheafFiber.obj F) := by
        by_contra hn
        have hm := hF (show (W.toScheme.algClosurePoint w ≫ W.ι) default ∈
            Scheme.etaleSheafSupport F from
          ⟨_, inferInstance, inferInstance, _, rfl, hn⟩)
        have hw : (W.toScheme.algClosurePoint w ≫ W.ι) default ∈ Set.range W.ι.base :=
          ⟨_, rfl⟩
        exact (hij ▸ hm) hw
      have hz' := hz.of_iso ((upperStarCompSheafFiberIso A W.ι
        (W.toScheme.algClosurePoint w)).app F)
      exact hz'.of_iso ((Scheme.pointSmallEtale (W.toScheme.algClosurePoint w)).uliftSheafFiberIso
        A |>.app ((upperStar A W.ι).obj F))
    · intro hF x hx
      rcases hx with ⟨Ω, hΩ, hclosed, s, rfl, hn⟩
      by_contra hs
      have hm : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range W.ι.base := by
        rw [Scheme.Opens.range_ι]
        change s (IsLocalRing.closedPoint Ω) ∉ Set.range i.base
        have he : s (IsLocalRing.closedPoint Ω) = s default :=
          congrArg s (Subsingleton.elim _ _)
        rw [he]
        exact hs
      let t := IsOpenImmersion.lift W.ι s
        (Scheme.range_base_subset_of_closedPoint_mem s hm)
      have ht : t ≫ W.ι = s := IsOpenImmersion.lift_fac _ _ _
      have hz := (Scheme.pointSmallEtale t).sheafFiber.map_isZero hF
      have hz' := hz.of_iso ((upperStarCompSheafFiberIso A W.ι t).app F).symm
      rw [ht] at hz'
      exact hn hz'
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    apply hsupport.mpr
    exact (isZero_upperStar_lowerStar_of_disjoint_range A W.ι i hji G).of_iso
      ((upperStar A W.ι).mapIso e).symm
  · intro hF
    have hz := hsupport.mp hF
    let η := (upperStarLowerStarAdjunction A i).unit.app F
    have hη : IsIso η := by
      apply isIso_of_isIso_upperStar_map A W.ι i hij η
      · exact hz.isIso
          (isZero_upperStar_lowerStar_of_disjoint_range A W.ι i hji
            ((upperStar A i).obj F)) _
      · change IsIso ((upperStar A i).map
          ((upperStarLowerStarAdjunction A i).unit.app F))
        rw [← IsIso.inv_eq_of_inv_hom_id
          ((upperStarLowerStarAdjunction A i).left_triangle_components F)]
        infer_instance
    exact ⟨(upperStar A i).obj F, ⟨(asIso η).symm⟩⟩

end AlgebraicGeometry.Etale

