/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Brauer
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.GaGmLowerStar
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# The Brauer group of a reduced curve

The Brauer group `H²(C_ét, 𝔾ₘ)` of a reduced curve `C` over an algebraically closed field
vanishes. Let `Zₚ` be the irreducible components of `C` with their reduced structure and
`νₚ : Yₚ ⟶ C` their normalizations (or the point `Zₚ` itself if `Zₚ` is a point). The map
`𝔾ₘ ⟶ ⨁ₚ νₚ_* 𝔾ₘ` is an isomorphism away from the finitely many closed points where two components
meet or where some `Yₚ ⟶ Zₚ` is not an isomorphism, hence bijective on `H²`; and
`H²(C, νₚ_* 𝔾ₘ) = H²(Yₚ, 𝔾ₘ)` vanishes since `Yₚ` is a smooth curve or a point.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_isReduced`: the Brauer
  group of a reduced curve over an algebraically closed field vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

open Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **One component of a reduced curve.** Let `Z` be an integral curve over an algebraically
closed field `k`. There is a finite morphism `n : Y ⟶ Z`, an isomorphism over a nonempty open
`W ⊆ Z`, with `Br(Y) = 0`: the normalization if `Z` has dimension one (a smooth curve), and the
spectrum of the residue field if `Z` is a point. -/
lemma exists_isFinite_isIso_subsingleton_cohomologicalBrauerGroup {Z : Scheme.{u}}
    [IsIntegral Z] (g : Z ⟶ Spec (.of k)) [IsCurve g] :
    ∃ (Y : Scheme.{u}) (n : Y ⟶ Z) (_ : IsFinite n) (W : Z.Opens), (W : Set Z).Nonempty ∧
      IsIso (n ∣_ W) ∧ Subsingleton Y.CohomologicalBrauerGroup := by
  by_cases hdim : topologicalKrullDim Z = 1
  · have := Z.isFinite_fromNormalization_of_locallyOfFiniteType g
    obtain ⟨W, hW, hiso⟩ := Z.exists_isIso_fromNormalization_restrict g
    refine ⟨Z.normalization, Z.fromNormalization, this, W, hW, hiso, ?_⟩
    have : Smooth (Z.fromNormalization ≫ g) := Scheme.smooth_fromNormalization_comp g hdim
    have : IsCurve (Z.fromNormalization ≫ g) :=
      { krullDim_le_one := ((Z.topologicalKrullDim_normalization g).trans hdim).le }
    exact subsingleton_cohomologicalBrauerGroup_of_smooth (Z.fromNormalization ≫ g)
  · refine ⟨Z, 𝟙 Z, inferInstance, ⊤, ⟨Classical.arbitrary Z, trivial⟩, ?_, ?_⟩
    · rw [morphismRestrict_id]
      exact IsIso.id _
    have h0 : topologicalKrullDim Z ≤ 0 := by
      have h1 : topologicalKrullDim Z < ((0 : ℕ) : WithBot ℕ∞) + 1 :=
        lt_of_le_of_ne (IsCurve.krullDim_le_one (f := g)) hdim
      exact ENat.WithBot.lt_add_one_iff.1 h1
    have : Subsingleton Z := subsingleton_of_topologicalKrullDim_le_zero h0
    let x : Z := Classical.arbitrary Z
    have hx : IsClosed ({x} : Set Z) := by
      rw [Set.eq_univ_of_forall fun y ↦ Set.mem_singleton_iff.mpr (Subsingleton.elim y x)]
      exact isClosed_univ
    have := Scheme.isAlgClosed_residueField_of_isClosed g x hx
    have := isClosed_singleton_iff_isClosedImmersion.mp hx
    have : Surjective (Z.fromSpecResidueField x) :=
      ⟨fun y ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : IsIso (Z.fromSpecResidueField x) := isIso_of_isClosedImmersion_of_surjective _
    have hb := cohomologyMap_bijective (Z.fromSpecResidueField x) Z.gmSheaf 2
    have := Scheme.subsingleton_H_of_isSepClosed (Z.residueField x)
      ((Z.fromSpecResidueField x)^*[AddCommGrpCat.{u + 1}].obj Z.gmSheaf) 1
    exact hb.injective.subsingleton

/-- **The Brauer group of a reduced curve vanishes.** For a reduced curve `C` over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Let `νₚ : Yₚ ⟶ C` be the
normalizations of the irreducible components `Zₚ` of `C` (with their reduced structure). The map
`𝔾ₘ ⟶ ⨁ₚ νₚ_* 𝔾ₘ` is an isomorphism away from a finite set of closed points
(`AlgebraicGeometry.Scheme.isIso_upperStar_map_gmSheafToLowerStarGmSheaf`), hence bijective on
`H²` (`AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map`), and
`H²(C, νₚ_* 𝔾ₘ) = Br(Yₚ) = 0`.
(blueprint: `lem-sc-brauer-zero-all-curves`, Step 2) -/
theorem subsingleton_cohomologicalBrauerGroup_of_isReduced (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsReduced C] : Subsingleton C.CohomologicalBrauerGroup := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  let ι := ↥(irreducibleComponents C)
  have : Finite ι := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).to_subtype
  have := Fintype.ofFinite ι
  -- the irreducible components `Z p`, with their reduced structure
  let I (p : ι) : C.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨p.1, isClosed_of_mem_irreducibleComponents _ p.2⟩
  let Z (p : ι) : Scheme.{u} := (I p).subscheme
  let c (p : ι) : Z p ⟶ C := (I p).subschemeι
  have hrange (p : ι) : Set.range (c p).base = p.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hirr (p : ι) : IrreducibleSpace (Z p) := by
    let h := (c p).isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range (c p).base) :=
      Subtype.irreducibleSpace ((hrange p).symm ▸ p.2.1)
    rw [irreducibleSpace_def]
    have := (IrreducibleSpace.isIrreducible_univ _).image h.symm h.symm.continuous.continuousOn
    rwa [Set.image_univ_of_surjective h.symm.surjective] at this
  have hint (p : ι) : IsIntegral (Z p) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcurve (p : ι) : IsCurve (c p ≫ f) :=
    { krullDim_le_one := ((c p).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans
        (IsCurve.krullDim_le_one (f := f)) }
  -- every point lies on a component
  have hcov (x : C) : ∃ p : ι, x ∈ p.1 := by
    obtain ⟨u, hu, hxu⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    exact ⟨⟨u, hu⟩, hxu rfl⟩
  -- the components and their finite modifications
  choose Y n hn W hW hiso hY using fun p ↦
    exists_isFinite_isIso_subsingleton_cohomologicalBrauerGroup (c p ≫ f)
  -- the good locus of each component: where it meets no other component and `n p` is an iso
  let O (p : ι) : Set (Z p) := (W p : Set (Z p)) ∩
    ⋂ q ∈ Finset.univ.filter (· ≠ p), ((c p).base ⁻¹' q.1)ᶜ
  have hOopen (p : ι) : IsOpen (O p) := by
    refine (W p).isOpen.inter (isOpen_biInter_finset fun q _ ↦ ?_)
    exact ((isClosed_of_mem_irreducibleComponents _ q.2).preimage (c p).continuous).isOpen_compl
  have hOne (p : ι) : (O p).Nonempty := by
    -- the generic point of `Z p` lies on no other component
    obtain ⟨w, hw⟩ := hW p
    let z₀ : Z p := genericPoint (Z p)
    refine ⟨z₀, ((genericPoint_spec (Z p)).mem_open_set_iff (W p).isOpen).mpr
      ⟨w, trivial, hw⟩, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hqp hmem
    have hle : p.1 ⊆ q.1 := by
      rw [← hrange p, ← Set.image_univ, ← (genericPoint_spec (Z p)).def]
      refine (image_closure_subset_closure_image (c p).continuous).trans
        (closure_minimal ?_ (isClosed_of_mem_irreducibleComponents _ q.2))
      simpa using hmem
    exact hqp (Subtype.ext ((p.2.2 q.2.1 hle).antisymm hle))
  have hnoeth (p : ι) : IsNoetherian (Z p) := by
    have : IsLocallyNoetherian (Z p) := LocallyOfFiniteType.isLocallyNoetherian (c p ≫ f)
    have : CompactSpace (Z p) := (quasiCompact_iff_compactSpace (c p ≫ f)).mp inferInstance
    exact ⟨⟩
  have hdimZ (p : ι) : topologicalKrullDim (Z p) ≤ 1 := IsCurve.krullDim_le_one (f := c p ≫ f)
  have hOfin (p : ι) : (O p)ᶜ.Finite :=
    (hOopen p).finite_compl_of_topologicalKrullDim_le_one (hdimZ p) (hOne p)
  have hOcl (p : ι) (z : Z p) (hz : z ∉ O p) : IsClosed ({z} : Set (Z p)) :=
    (hOopen p).isClosed_singleton_of_mem_compl (hdimZ p) (hOne p) hz
  -- the bad set `S`
  let S : Set C := ⋃ p, (c p).base '' (O p)ᶜ
  have hSfin : S.Finite := Set.finite_iUnion fun p ↦ (hOfin p).image _
  have hScl (x : C) (hx : x ∈ S) : IsClosed ({x} : Set C) := by
    obtain ⟨p, z, hz, rfl⟩ := Set.mem_iUnion.1 hx
    simpa using (c p).isClosedEmbedding.isClosedMap _ (hOcl p z hz)
  have hSclosed : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion hScl
  let U : C.Opens := ⟨Sᶜ, hSclosed.isOpen_compl⟩
  -- the pieces `V p` of `U`, away from the other components
  let V (p : ι) : C.Opens := ⟨Sᶜ ∩ ⋂ q ∈ Finset.univ.filter (· ≠ p), (q.1)ᶜ,
    hSclosed.isOpen_compl.inter (isOpen_biInter_finset fun q _ ↦
      (isClosed_of_mem_irreducibleComponents _ q.2).isOpen_compl)⟩
  have hVU (p : ι) : V p ≤ U := fun _ hx ↦ hx.1
  have hVZ (p : ι) (x : C) (hx : x ∈ V p) : x ∈ Set.range (c p).base := by
    obtain ⟨q, hq⟩ := hcov x
    by_cases hqp : q = p
    · exact hqp ▸ (hrange q).symm ▸ hq
    · refine absurd hq ?_
      have := hx.2
      simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this q hqp
  have hVO (p : ι) (z : Z p) (hz : (c p).base z ∈ V p) : z ∈ O p := by
    by_contra h
    exact hz.1 (Set.mem_iUnion.2 ⟨p, z, h, rfl⟩)
  have hUV (x : C) (hx : x ∈ U) : ∃ p, x ∈ V p := by
    obtain ⟨p, hp⟩ := hcov x
    refine ⟨p, hx, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hqp hxq
    obtain ⟨z, rfl⟩ : x ∈ Set.range (c p).base := (hrange p).symm ▸ hp
    refine hx (Set.mem_iUnion.2 ⟨p, z, fun hz ↦ ?_, rfl⟩)
    have := hz.2
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this q hqp hxq
  have hdisj (p q : ι) (hqp : q ≠ p) :
      Disjoint (Set.range (V p).ι.base) (Set.range (n q ≫ c q).base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_right]
    rintro _ ⟨y, rfl⟩ hy
    have := hy.2
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    refine this q hqp ?_
    rw [← hrange q]
    exact ⟨(n q).base y, rfl⟩
  have hisoV (p : ι) : IsIso ((n p ≫ c p) ∣_ V p) := by
    rw [morphismRestrict_comp]
    have h1 : IsIso (n p ∣_ (c p ⁻¹ᵁ V p)) :=
      isIso_morphismRestrict_of_le (n p) (fun z hz ↦ (hVO p z hz).1) (hiso p)
    have : Surjective (c p ∣_ V p) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨z, hz⟩ := hVZ p y.1 y.2
      refine ⟨⟨z, show (c p).base z ∈ V p from hz ▸ y.2⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe _ _ _).trans hz
    have : IsClosedImmersion (c p ∣_ V p) :=
      IsZariskiLocalAtTarget.restrict (inferInstanceAs (IsClosedImmersion (c p))) _
    have h2 : IsIso (c p ∣_ V p) := isIso_of_isClosedImmersion_of_surjective _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  -- the comparison map `𝔾ₘ ⟶ ⨁ₚ νₚ_* 𝔾ₘ`
  have : HasFiniteBiproducts (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let ν (p : ι) : Y p ⟶ C := n p ≫ c p
  let G (p : ι) : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (ν p)_*[AddCommGrpCat.{u + 1}].obj (Y p).gmSheaf
  let φ : C.gmSheaf ⟶ ⨁ G := biproduct.lift fun p ↦ Scheme.gmSheafToLowerStarGmSheaf (ν p)
  have hG (p : ι) : Subsingleton (Sheaf.H (G p) 2) := by
    have := hY p
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (Y p).smallEtaleTopology AddCommGrpCat.{u + 1})).obj
        (Y p).gmSheaf) 2) := this
    exact (bijective_edgeMap_of_isFinite (ν p) _ 2).injective.subsingleton
  have hφ : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map φ) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun p ↦ C.homOfLE (hVU p)) (fun x ↦ ?_) _ fun p ↦ ?_
    · obtain ⟨p, hp⟩ := hUV x.1 x.2
      exact ⟨p, ⟨x.1, hp⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
    have e := upperStarComp AddCommGrpCat.{u + 1} (C.homOfLE (hVU p)) U.ι (V p).ι
      (Scheme.homOfLE_ι _ _).symm
    change IsIso (((U.ι)^*[AddCommGrpCat.{u + 1}] ⋙
      (C.homOfLE (hVU p))^*[AddCommGrpCat.{u + 1}]).map φ)
    rw [← NatIso.isIso_map_iff e φ]
    let P := ((V p).ι)^*[AddCommGrpCat.{u + 1}]
    have hz (q : ι) (hqp : q ≠ p) : IsZero (P.obj (G q)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ (V p).ι (ν q) (hdisj p q hqp) _
    have hπ : IsIso (P.map (biproduct.π G p)) := by
      refine ⟨P.map (biproduct.ι G p), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G), P.map_sum,
          Finset.sum_eq_single p (fun q _ hqp ↦ ?_) (by simp)]
        rw [P.map_comp, (hz q hqp).eq_zero_of_tgt (P.map (biproduct.π G q)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have : IsIso (ν p ∣_ V p) := hisoV p
    have hunit : IsIso (P.map (Scheme.gmSheafToLowerStarGmSheaf (ν p))) :=
      Scheme.isIso_upperStar_map_gmSheafToLowerStarGmSheaf (ν p) (V p)
    have : IsIso (P.map φ ≫ P.map (biproduct.π G p)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  have hSU : (U : Set C)ᶜ = S := compl_compl S
  have hsep (x : C) (hx : x ∉ U) : IsSepClosed (C.residueField x) := by
    have := Scheme.isAlgClosed_residueField_of_isClosed f x (hScl x (hSU ▸ hx))
    infer_instance
  have hb := bijective_H_map_of_isIso_upperStar_map U (hSU ▸ hSfin)
    (fun x hx ↦ hScl x (hSU ▸ hx)) hsep φ hφ 0
  have : Subsingleton (Sheaf.H (⨁ G) 2) :=
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit G) 2).toEquiv.subsingleton
  exact hb.injective.subsingleton

end AlgebraicGeometry.IsCurve
