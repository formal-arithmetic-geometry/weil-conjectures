/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Product
public import WeilConjectures.TraceFormula.Specialization.DeformationProperPoint
public import WeilConjectures.TraceFormula.Specialization.ExchangeOnProperBdc

/-!

# The compact-support exchange of the support on a component of the fixed locus

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y` (`b ≫ j ≫ ι = y`). The closed embedding `B ⊂ F ⊂ C` (`ι ∘ j`) induces a morphism
of deformation models `𝒟_B ⟶ 𝒞` (`componentModelHom`, deformations along `ker b` and `ker y`).
If `B` is proper with one point, its morphism of total spaces and the composite `𝒟_B ⟶ 𝒞̄` with
the open immersion into the compactification `𝒞̄ = D_{Z'} C̄ ×_{𝔸¹} S` are proper
(`isProper_componentModelHom_total`, `isProper_componentModelHom_comp_total`), and closed
immersions when `B ⊂ C` is closed, e.g. for `j` an open immersion
(`isClosedImmersion_componentModelHom_total`, `isClosedImmersion_componentModelHom_comp_total`,
`isClosedImmersion_comp_ι`).

On the objects `(ι ∘ j)_* N` the compact-support exchange `ν_c = supportCompactSupportExchange` of
the support is then the pushforward exchange of `B ⟶ C̄ ⟶ X ⨯ X` after `c'_!(χ_{ι∘j})`
(`supportCompactSupportExchange_app_lowerStar`, an instance of
`compactSupportExchangeOfCompactification_app_lowerStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)

include hb in
/-- Functions vanishing at `y` pull back along `B ⊂ F ⊂ C` to functions vanishing at `b`. -/
lemma map_siteIdeal_le_ker_component :
    ∀ ⦃U' : B.left.AffineZariskiSite⦄ ⦃U : c.C.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (j ≫ F.ι).left ⁻¹ᵁ U.1),
      (y.left.ker.siteIdeal U).map ((j ≫ F.ι).left.appLE U.1 U'.1 hU).hom ≤
        b.left.ker.siteIdeal U' := by
  refine IdealSheafData.map_siteIdeal_le_of_comap_le _ ?_
  rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, hb]

/-- The morphism of deformation models `𝒟_B ⟶ 𝒞` over `B ⊂ F ⊂ C` (`ι ∘ j`), for the deformations
of `B` along `ker b` and of `C` along `ker y`. -/
noncomputable def componentModelHom :=
  deformationModelHom (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k'

include hb in
/-- If `B` is proper with underlying set `{b}`, the morphism of total spaces of
`componentModelHom` is proper: `𝒟_B` is proper over the trait and `𝒞` is separated over it. -/
lemma isProper_componentModelHom_total [IsProper B.hom]
    (hbr : Set.range b.left.base = Set.univ) :
    IsProper (componentModelHom k' j hb).total := by
  have := isProper_deformationTotalToTrait_ker B k' hbr
  have : IsProper ((componentModelHom k' j hb).total ≫
      deformationTotalToTrait c.C y.left.ker k') := by
    erw [deformationTotalMap_toTrait]
    infer_instance
  exact IsProper.of_comp _ (deformationTotalToTrait c.C y.left.ker k')

include hb in
/-- If `B` is proper with underlying set `{b}`, the morphism of total spaces `𝒟_B ⟶ 𝒞̄` of the
composite of `componentModelHom` with the open immersion `𝒞 ⟶ 𝒞̄ = D_{Z'} C̄ ×_{𝔸¹} S` is
proper. -/
lemma isProper_componentModelHom_comp_total [IsProper B.hom]
    (hbr : Set.range b.left.base = Set.univ) :
    IsProper ((componentModelHom k' j hb).comp (supportClosureOpenModelHom c y hc k')).total := by
  have := isProper_deformationTotalToTrait_ker B k' hbr
  have : IsProper ((deformationTotalMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k' ≫
      deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k') ≫
      deformationTotalToTrait (supportClosure c) (supportClosureIdeal c y) k') := by
    rw [Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait]
    infer_instance
  exact IsProper.of_comp (deformationTotalMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k' ≫
    deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k')
    (deformationTotalToTrait (supportClosure c) (supportClosureIdeal c y) k')

/-- An open immersion `j : B ⟶ F` from a proper `k`-scheme is a closed immersion. -/
lemma isClosedImmersion_left_of_isProper [IsOpenImmersion j.left] [IsProper B.hom] :
    IsClosedImmersion j.left := by
  have : UniversallyClosed (j.left ≫ F.F.hom) := by rw [Over.w j]; infer_instance
  have : UniversallyClosed j.left := UniversallyClosed.of_comp_of_isSeparated j.left F.F.hom
  exact IsClosedImmersion.of_isPreimmersion _ j.left.isClosedMap.isClosed_range

/-- For `B` proper and `j` an open immersion, `B ⊂ F ⊂ C` is a closed immersion. -/
lemma isClosedImmersion_comp_ι [IsOpenImmersion j.left] [IsProper B.hom] :
    IsClosedImmersion (j ≫ F.ι).left :=
  have := isClosedImmersion_left_of_isProper j
  inferInstanceAs (IsClosedImmersion (j.left ≫ F.ι.left))

include hb in
/-- The preimage of `y` under the closed immersion `B ⊂ F ⊂ C` is the point `b`. -/
lemma comap_ker_component [IsClosedImmersion (j ≫ F.ι).left] :
    y.left.ker.comap (j ≫ F.ι).left = b.left.ker := by
  have : IsClosedImmersion y.left := isClosedImmersion_of_comp_eq_id c.C.hom y.left (Over.w y)
  have hP : IsPullback b.left (𝟙 _) (j ≫ F.ι).left y.left :=
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 _) (snd := b.left)
      ⟨by rw [Category.id_comp, ← Over.comp_left, hb]⟩).flip
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion, ← hP.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

include hb in
/-- If `B ⊂ F ⊂ C` is a closed immersion, so is the morphism of total spaces of
`componentModelHom`: the deformation space of `B` along `ker b = (ker y)|_B` is closed in that of
`C` (`IdealSheafData.isClosedImmersion_deformationSpaceMap`). -/
lemma isClosedImmersion_componentModelHom_total [IsClosedImmersion (j ≫ F.ι).left] :
    IsClosedImmersion (componentModelHom k' j hb).total :=
  have := IdealSheafData.isClosedImmersion_deformationSpaceMap (j ≫ F.ι).left y.left.ker
    b.left.ker (map_siteIdeal_le_ker_component j hb) (comap_ker_component j hb).symm
  MorphismProperty.of_isPullback
    (isPullback_deformationTotalMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k').flip this

include hb in
/-- If moreover `B` is proper with underlying set `{b}`, the morphism of total spaces `𝒟_B ⟶ 𝒞̄`
of the composite with the open immersion `𝒞 ⟶ 𝒞̄` is a closed immersion: it is an immersion
and proper (`isProper_componentModelHom_comp_total`). -/
lemma isClosedImmersion_componentModelHom_comp_total [IsClosedImmersion (j ≫ F.ι).left]
    [IsProper B.hom] (hbr : Set.range b.left.base = Set.univ) :
    IsClosedImmersion
      ((componentModelHom k' j hb).comp (supportClosureOpenModelHom c y hc k')).total := by
  have := isProper_componentModelHom_comp_total hc k' j hb hbr
  have := isClosedImmersion_componentModelHom_total k' j hb
  have : IsOpenImmersion (supportClosureOpenModelHom c y hc k').total :=
    isOpenImmersion_deformationTotalMap (supportClosureι c) hc.map_siteIdeal_le_ker k'
      hc.comap_supportClosureIdeal
  have : IsPreimmersion
      ((componentModelHom k' j hb).comp (supportClosureOpenModelHom c y hc k')).total :=
    inferInstanceAs (IsPreimmersion (_ ≫ _))
  exact IsClosedImmersion.of_isPreimmersion _
    (Scheme.Hom.isClosedMap _).isClosed_range

variable [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']

/-- The special fibre `p'` of `c̄` is proper if `D_{Z'} C̄ ⟶ D_x X ×_{𝔸¹} D_x X` is. -/
instance isProper_supportClosureSpecialMap_left [IsProper (supportClosureSpaceMap c y)] :
    IsProper (supportClosureSpecialMap c y k').left :=
  isProper_supportClosureSpecialMap k' (isProper_deformationProdLiftTotal k' _ _ _ _)

variable [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [IsProper (supportClosureSpaceMap c y)]

/-- **The compact-support exchange `ν_c` of the support on pushforwards from `B`** (step (B) of
Varshavsky's argument): for `ν_c = supportCompactSupportExchange` and `N : Dᵇc(B)`, the identity of
`compactSupportExchangeOfCompactification_app_lowerStar` for the morphism of models
`componentModelHom` over `B ⊂ F ⊂ C`: on `(ι ∘ j)_* N`, `ν_c` read through the composition
isomorphisms is the pushforward exchange of `(𝒟_B ⟶ 𝒞 ⟶ 𝒞̄) ⟶ 𝒳 ×_S 𝒳` after `c'_!(χ_{ι∘j})`, given
the ambient identity `hC` of `compactSupportExchangeOfCompactification_app_lowerStar` at `N`. -/
theorem supportCompactSupportExchange_app_lowerStar
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hC : hypothesisOf (compactSupportExchangeOfCompactification_app_lowerStar ℓ
      ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel c.C y.left.ker k')
        (deformationModel_exists_comp_ε c.C y.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k'))
      (f := c.support) (h := supportClosureι c)
      (by rw [prodLift_supportClosureMap, supportClosureι_map])
      (f' := (hc.specialCorrespondence k').support) (h' := hc.supportClosureSpecialι k')
      (hc.supportClosureSpecialι_comp k') (supportClosureOpenModelHom c y hc k')
      (supportClosureProperModelHom c y k')
      (isIsoOn_supportClosureProperModelHom_pushforwardExchange k'
        (isProper_deformationProdLiftTotal k' _ _ _ _))
      (componentModelHom k' j hb) (hc.supportCompactSupportExchange k') rfl N)) :
    type_of% (compactSupportExchangeOfCompactification_app_lowerStar ℓ
      ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel c.C y.left.ker k')
        (deformationModel_exists_comp_ε c.C y.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k'))
      (f := c.support) (h := supportClosureι c)
      (by rw [prodLift_supportClosureMap, supportClosureι_map])
      (f' := (hc.specialCorrespondence k').support) (h' := hc.supportClosureSpecialι k')
      (hc.supportClosureSpecialι_comp k') (supportClosureOpenModelHom c y hc k')
      (supportClosureProperModelHom c y k')
      (isIsoOn_supportClosureProperModelHom_pushforwardExchange k'
        (isProper_deformationProdLiftTotal k' _ _ _ _))
      (componentModelHom k' j hb) (hc.supportCompactSupportExchange k') rfl N hC) := by
  exact compactSupportExchangeOfCompactification_app_lowerStar ℓ
      ((deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel c.C y.left.ker k')
        (deformationModel_exists_comp_ε c.C y.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (isTraitModel_deformationProdModel X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k')
        (deformationProdModel_exists_comp_ε X (y ≫ c.c₁).left.ker X (y ≫ c.c₁).left.ker k'))
      (f := c.support) (h := supportClosureι c)
      (by rw [prodLift_supportClosureMap, supportClosureι_map])
      (f' := (hc.specialCorrespondence k').support) (h' := hc.supportClosureSpecialι k')
      (hc.supportClosureSpecialι_comp k') (supportClosureOpenModelHom c y hc k')
      (supportClosureProperModelHom c y k')
      (isIsoOn_supportClosureProperModelHom_pushforwardExchange k'
        (isProper_deformationProdLiftTotal k' _ _ _ _))
      (componentModelHom k' j hb) (hc.supportCompactSupportExchange k') rfl N hC

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
