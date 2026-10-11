/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Compactification.EliminationOfIndeterminacy
public import WeilConjectures.Compactification.StrictTransformBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Topology.Spectral.Prespectral

/-!

# Isomorphism near the closure of a boundary piece

This file proves the **isomorphism near a boundary closure** (Stacks Project Tag 0F3W;
blueprint `thm:0F3W`, `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`):

- `AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure`: a
  proper morphism which is an isomorphism over a neighbourhood of a closed piece `T` of
  `U` acquires, after a `U`-admissible blow-up, a strict transform which is an
  isomorphism over a neighbourhood of the closure of `T`.

It is used for the improved comparison projection of the two-open compactification
theorem, and rests on elimination of indeterminacy
(`WeilConjectures.Compactification.EliminationOfIndeterminacy`, Tag 081S).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W;
blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection of
the two-open compactification theorem).

The proof runs as follows. Inside `U`, constructible separation
(`PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ`) separates `T` from
the complement of the maximal isomorphism open `M` of `q`, producing a quasi-compact
open `V₂` of `X` with `T ⊆ V₂ ⊆ U ⊓ M` and a constructible closed decomposition of `U`.
The boundary-separation blow-up `X₁ ⟶ X` (`exists_admissibleBlowup_disjoint_closures`,
Tag 0F3V) then separates the closure of the inverse image of `T` from the closure of
the inverse image of `U \ V₂`, and a second constructible separation, now in `X₁`,
produces a **quasi-compact** open `A ⊆ X₁` containing the first closure and missing the
second; consequently every point of `A` over `U` lies over `V₂`.

Over `X₁` the canonical lift of `q` is an isomorphism above `V₂`, so eliminating its
indeterminacy (`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`, Tag 081S)
gives a finite-type centre whose support misses the locus above `V₂`, hence also
`A ∩ π₁⁻¹(U)`. Gluing that centre across `A` and the locus above `U`
(`Scheme.IdealSheafData.exists_finiteType_comap_eq_of_disjoint`, Tag 080M) and composing
with the first blow-up (`Scheme.IdealSheafData.exists_blowup_comp_base_change`, Tag 080B)
produces a single `U`-admissible centre `K` on `X`, together with identifications of
both `K.blowup` and `(K.comap q).blowup` with their counterparts upstairs.

Finally Tag 080E (`Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`)
turns the strict transform of `q` along `K.blowupMap` into the canonical lift
`(K.comap q).blowup ⟶ K.blowup`, and the localization of canonical lifts
(`Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens`) identifies that lift over
the copy of `A` with the open immersion produced by Tag 081S. The neighbourhood `N'` is
the range of the resulting partial section; it contains the closure of the inverse
image of `T` because that closure lies over `A` and inside the (closed, since `q` is
proper) range of the strict transform. No scheme-theoretic density argument is used. -/
theorem exists_admissibleBlowup_isIso_strictTransformMap_near_closure
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ (B : IsAdmissible X U) (N' : B.I.blowup.Opens),
      closure (B.I.blowupMap ⁻¹' T) ⊆ (N' : Set B.I.blowup) ∧
      IsIso (strictTransformMap q B.I.blowupMap B.preservedOpen ∣_ N') := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  -- Step 0: `T` lies in the maximal isomorphism open `M` of `q`, and `M` lies in the
  -- image of `q`.
  set M : X.Opens := q.maximalIsomorphismOpen with hMdef
  have hqM : IsIso (q ∣_ M) := q.isIso_restrict_maximalIsomorphismOpen
  have hTM : T ⊆ (M : Set X) := hTN.trans fun _ hx ↦ q.le_maximalIsomorphismOpen hN hx
  have hMrange : (M : Set X) ⊆ Set.range q := by
    intro x hx
    have := hqM
    obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso (q ∣_ M))).surjective ⟨x, hx⟩
    refine ⟨(q ⁻¹ᵁ M).ι z, ?_⟩
    calc q ((q ⁻¹ᵁ M).ι z) = ((q ⁻¹ᵁ M).ι ≫ q) z := (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((q ∣_ M) ≫ M.ι) z := by rw [morphismRestrict_ι]
      _ = M.ι ((q ∣_ M) z) := Scheme.Hom.comp_apply _ _ _
      _ = x := congrArg Subtype.val (by simpa using hz)
  -- Step 1: constructible separation of `T` from the complement of `M` inside `U`.
  obtain ⟨O₁, O₂, hO₁o, hO₂o, hO₁c, hO₂c, hO₁T, hO₂M, hOcov⟩ :=
    PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ (X := U.toScheme)
      (T₁ := U.ι ⁻¹' T) (T₂ := U.ι ⁻¹' (M : Set X)ᶜ) hT
      (M.isOpen.isClosed_compl.preimage U.ι.continuous)
      (Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ (hTM h₁))
  set V₂ : X.Opens := U.ι ''ᵁ (⟨O₂, hO₂o⟩ : U.toScheme.Opens) with hV₂def
  have hV₂U : V₂ ≤ U := by
    rintro x ⟨y, -, rfl⟩
    have : U.ι y ∈ Set.range U.ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hV₂M : V₂ ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    by_contra hcon
    exact Set.disjoint_left.mp hO₂M hy hcon
  have hV₂c : IsCompact (V₂ : Set X) := hO₂c.image U.ι.continuous
  have hTcl : IsClosed (O₁ᶜ : Set U.toScheme) := hO₁o.isClosed_compl
  have hEcl : IsClosed (O₂ᶜ : Set U.toScheme) := hO₂o.isClosed_compl
  have hTsub : U.ι ⁻¹' T ⊆ (O₁ᶜ : Set U.toScheme) := fun _ hy hy₁ ↦
    Set.disjoint_left.mp hO₁T hy₁ hy
  have hTEdisj : Disjoint (O₁ᶜ : Set U.toScheme) (O₂ᶜ : Set U.toScheme) := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    rcases Set.eq_univ_iff_forall.mp hOcov y with h | h
    · exact hy₁ h
    · exact hy₂ h
  have hTimg : T ⊆ U.ι '' (O₁ᶜ : Set U.toScheme) := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact hTU hx
    exact ⟨y, hTsub hx, rfl⟩
  -- Step 2: the boundary-separation blow-up (Tag 0F3V).
  obtain ⟨B₁, hB₁disj⟩ := exists_admissibleBlowup_disjoint_closures hU hTcl hEcl
    (by rwa [compl_compl]) (by rwa [compl_compl]) hTEdisj
  have : IsProper B₁.I.blowupMap := B₁.isProper_blowupMap
  have : QuasiCompact B₁.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap B₁.finiteType
  have : CompactSpace B₁.I.blowup :=
    QuasiCompact.compactSpace_of_compactSpace B₁.I.blowupMap
  have : QuasiSeparatedSpace B₁.I.blowup :=
    quasiSeparatedSpace_of_quasiSeparated B₁.I.blowupMap
  -- Step 3: a quasi-compact open of the blow-up around the closure of the inverse
  -- image of `T`, disjoint from the closure of the inverse image of the boundary.
  obtain ⟨A₁, A₂, -, hA₂o, -, hA₂c, hA₁T, hA₂E, hAcov⟩ :=
    PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ
      (X := B₁.I.blowup) isClosed_closure isClosed_closure hB₁disj
  set A : (B₁.I.blowup).Opens := ⟨A₂, hA₂o⟩ with hAdef
  have hCTA : closure (B₁.I.blowupMap ⁻¹' (U.ι '' (O₁ᶜ : Set U.toScheme))) ⊆
      (A : Set B₁.I.blowup) := by
    intro x hx
    rcases Set.eq_univ_iff_forall.mp hAcov x with h | h
    · exact absurd hx (Set.disjoint_left.mp hA₁T h)
    · exact h
  have hAUV : ∀ x : B₁.I.blowup, x ∈ (A : Set B₁.I.blowup) →
      B₁.I.blowupMap x ∈ (U : Set X) → B₁.I.blowupMap x ∈ (V₂ : Set X) := by
    intro x hxA hxU
    by_contra hcon
    obtain ⟨y, hy⟩ : B₁.I.blowupMap x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact hxU
    have hyE : y ∈ (O₂ᶜ : Set U.toScheme) := fun hy₂ ↦ hcon (hy ▸ ⟨y, hy₂, rfl⟩)
    exact Set.disjoint_left.mp hA₂E hxA
      (subset_closure (Set.mem_preimage.mpr ⟨y, hyE, hy⟩))
  -- Step 4: the canonical lift of `q` to the first blow-up, and its properness.
  have hcqft : (B₁.I.comap q).ofFiniteType := B₁.finiteType.comap q
  have : IsProper (B₁.I.comap q).blowupMap :=
    (B₁.I.comap q).isProper_blowupMap fun V ↦ hcqft V le_top
  obtain ⟨lam₁, hlam₁⟩ := B₁.I.exists_lift_blowup
    (t := (B₁.I.comap q).blowupMap ≫ q)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (B₁.I.comap q).isInvertible_comap_blowupMap)
  have : IsProper (lam₁ ≫ B₁.I.blowupMap) := by rw [hlam₁]; infer_instance
  have : IsProper lam₁ := IsProper.of_comp lam₁ B₁.I.blowupMap
  -- `lam₁` is an isomorphism over the locus above `V₂`
  have hdisjV₂ : Disjoint (V₂ : Set X) (B₁.I.support : Set X) :=
    B₁.disjoint_support.mono_left fun _ hx ↦ hV₂U hx
  have hπ₁V₂ : IsIso (B₁.I.blowupMap ∣_ V₂) := B₁.I.isIso_blowupMap_restrict hdisjV₂
  have hqV₂ : IsIso (q ∣_ V₂) := Scheme.Hom.isIso_restrict_of_le hV₂M hqM
  have hπZV₂ : IsIso ((B₁.I.comap q).blowupMap ∣_ (q ⁻¹ᵁ V₂)) := by
    refine (B₁.I.comap q).isIso_blowupMap_restrict ?_
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap] at hzs
    exact Set.disjoint_left.mp hdisjV₂ hz hzs
  have hlam₁iso : IsIso (lam₁ ∣_ (B₁.I.blowupMap ⁻¹ᵁ V₂)) := by
    refine isIso_morphismRestrict_of_comp lam₁ B₁.I.blowupMap hlam₁ V₂ hπ₁V₂ ?_
    have := hπZV₂
    have := hqV₂
    rw [morphismRestrict_comp]
    infer_instance
  -- Step 5: elimination of indeterminacy on the blow-up, over the locus above `V₂`.
  obtain ⟨B', hB'⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap
    (B₁.I.blowupMap.isCompact_preimage hV₂c) lam₁ hlam₁iso
  obtain ⟨eC, -, heC⟩ := B'.I.exists_blowup_comap_iso_strictTransform lam₁
  set lamC : (B'.I.comap lam₁).blowup ⟶ B'.I.blowup :=
    eC.hom ≫ strictTransformMap lam₁ B'.I.blowupMap B'.I.support.compl with hlamCdef
  have : IsOpenImmersion lamC := by
    have := hB'
    rw [hlamCdef]
    infer_instance
  -- Step 6: glue the centre across `A` and the locus above `U` (Tag 080M).
  set JA : A.toScheme.IdealSheafData := B'.I.comap A.ι with hJAdef
  have hJAft : JA.ofFiniteType := B'.finiteType.comap_of_isOpenImmersion A.ι
  have hJAdisj : Disjoint
      ((A.ι ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ U) : A.toScheme.Opens) : Set A.toScheme)
      (JA.support : Set A.toScheme) := by
    rw [Set.disjoint_left]
    intro y hyU hyJ
    rw [hJAdef, Scheme.IdealSheafData.coe_support_comap] at hyJ
    have hyA : A.ι y ∈ (A : Set B₁.I.blowup) := by
      have : A.ι y ∈ Set.range A.ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact Set.disjoint_left.mp B'.disjoint_support (hAUV _ hyA hyU) hyJ
  obtain ⟨D, hDft, hDA, hDdisj⟩ :=
    Scheme.IdealSheafData.exists_finiteType_comap_eq_of_disjoint hA₂c
      (B₁.I.blowupMap.isCompact_preimage hU) JA hJAft hJAdisj
  -- Step 7: composition of the two blow-ups, compatibly with base change along `q`.
  obtain ⟨K, hKft, hKsupp, al, hal, hbc⟩ :=
    Scheme.IdealSheafData.exists_blowup_comp_base_change B₁.I B₁.finiteType D hDft
  obtain ⟨be, hbe, -⟩ := hbc q lam₁ hlam₁
  have hKdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hx | ⟨x', hx', rfl⟩
    · exact Set.disjoint_left.mp B₁.disjoint_support hxU hx
    · exact Set.disjoint_left.mp hDdisj hxU hx'
  have hKcqft : (K.comap q).ofFiniteType := hKft.comap q
  have : IsProper K.blowupMap := K.isProper_blowupMap fun V ↦ hKft V le_top
  have : IsProper (K.comap q).blowupMap :=
    (K.comap q).isProper_blowupMap fun V ↦ hKcqft V le_top
  -- Step 8: the canonical lifts on the composite blow-up and their comparison.
  obtain ⟨eK, -, heK⟩ := K.exists_blowup_comap_iso_strictTransform q
  set st : K.strictTransform q ⟶ K.blowup :=
    strictTransformMap q K.blowupMap K.support.compl with hstdef
  set lamK : (K.comap q).blowup ⟶ K.blowup := eK.hom ≫ st with hlamKdef
  have hlamK : lamK ≫ K.blowupMap = (K.comap q).blowupMap ≫ q := heK
  have : IsProper (lamK ≫ K.blowupMap) := by rw [hlamK]; infer_instance
  have : IsProper lamK := IsProper.of_comp lamK K.blowupMap
  obtain ⟨lamD, hlamD⟩ := D.exists_lift_blowup (t := (D.comap lam₁).blowupMap ≫ lam₁)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (D.comap lam₁).isInvertible_comap_blowupMap)
  have hcompat : be.inv ≫ lamK = lamD ≫ al.inv := by
    have hbeinv : be.inv ≫ (K.comap q).blowupMap =
        (D.comap lam₁).blowupMap ≫ (B₁.I.comap q).blowupMap := by
      rw [← hbe, Iso.inv_hom_id_assoc]
    have halinv : al.inv ≫ K.blowupMap = D.blowupMap ≫ B₁.I.blowupMap := by
      rw [← hal, Iso.inv_hom_id_assoc]
    refine K.hom_ext_of_isInvertible_comap
      (t := be.inv ≫ (K.comap q).blowupMap ≫ q) ?_ ?_ ?_
    · simp only [Scheme.IdealSheafData.comap_comp]
      exact ((K.comap q).isInvertible_comap_blowupMap).comap_of_isOpenImmersion be.inv
    · rw [Category.assoc, hlamK]
    · rw [Category.assoc, halinv, ← Category.assoc, hlamD, Category.assoc, hlam₁,
        ← Category.assoc, ← Category.assoc be.inv, hbeinv]
  have hlamKal : lamK ≫ al.hom = be.hom ≫ lamD := by
    calc lamK ≫ al.hom = (be.hom ≫ be.inv ≫ lamK) ≫ al.hom := by
          rw [Iso.hom_inv_id_assoc]
      _ = be.hom ≫ (be.inv ≫ lamK) ≫ al.hom := by rw [Category.assoc]
      _ = be.hom ≫ (lamD ≫ al.inv) ≫ al.hom := by rw [hcompat]
      _ = be.hom ≫ lamD := by rw [Category.assoc, al.inv_hom_id, Category.comp_id]
  -- Step 8b: localizing the two lifts over `A`; they agree there by construction.
  obtain ⟨mu, hmu⟩ := JA.exists_lift_blowup
    (t := (JA.comap (lam₁ ∣_ A)).blowupMap ≫ (lam₁ ∣_ A))
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (JA.comap (lam₁ ∣_ A)).isInvertible_comap_blowupMap)
  obtain ⟨hC, hC', hCOI, hC'OI, hCsq, -, -⟩ :=
    Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens B'.I lam₁ A rfl heC hmu
  have := hCOI
  have := hC'OI
  have : IsOpenImmersion mu := by
    have : IsOpenImmersion (mu ≫ hC) := by
      rw [← hCsq]
      infer_instance
    exact IsOpenImmersion.of_comp mu hC
  obtain ⟨hD, hD', hDOI, hD'OI, hDsq, hDrange, hD'range⟩ :=
    Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens D lam₁ A hDA hlamD hmu
  have := hDOI
  have := hD'OI
  -- Step 9: the partial section of the strict transform over the copy of `A`.
  set m : (JA.comap (lam₁ ∣_ A)).blowup ⟶ (K.comap q).blowup := hD' ≫ be.inv with hmdef
  have : IsOpenImmersion m := by rw [hmdef]; infer_instance
  have hjeq : m ≫ lamK = mu ≫ hD ≫ al.inv := by
    rw [hmdef, Category.assoc, hcompat, ← Category.assoc, hDsq, Category.assoc]
  have : IsOpenImmersion (m ≫ lamK) := by rw [hjeq]; infer_instance
  have hD'pre : Set.range hD' = lamD ⁻¹' Set.range hD := by
    rw [hD'range, hDrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have hD'pre' : Set.range hD' = lamD ⁻¹' Set.range (mu ≫ hD) := by
    refine subset_antisymm ?_ ?_
    · rintro - ⟨w, rfl⟩
      exact ⟨w, by rw [← Scheme.Hom.comp_apply, ← hDsq, Scheme.Hom.comp_apply]⟩
    · intro x hx
      rw [hD'pre]
      obtain ⟨w, hw⟩ := hx
      exact ⟨mu w, by rw [← Scheme.Hom.comp_apply]; exact hw⟩
  have hmrange : Set.range m = lamK ⁻¹' Set.range (m ≫ lamK) := by
    refine subset_antisymm ?_ ?_
    · rintro - ⟨w, rfl⟩
      exact ⟨w, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · intro y hy
      rw [hjeq] at hy
      obtain ⟨w, hw⟩ := hy
      have hbeinvhom : be.inv (be.hom y) = y := by
        rw [← Scheme.Hom.comp_apply, be.hom_inv_id]
        rfl
      have hx : lamD (be.hom y) ∈ Set.range (mu ≫ hD) := by
        refine ⟨w, al.inv.isOpenEmbedding.injective ?_⟩
        calc al.inv ((mu ≫ hD) w)
            = ((mu ≫ hD) ≫ al.inv) w := (Scheme.Hom.comp_apply _ _ _).symm
          _ = lamK y := hw
          _ = lamK (be.inv (be.hom y)) := by rw [hbeinvhom]
          _ = (be.inv ≫ lamK) (be.hom y) := (Scheme.Hom.comp_apply _ _ _).symm
          _ = (lamD ≫ al.inv) (be.hom y) := by rw [hcompat]
          _ = al.inv (lamD (be.hom y)) := Scheme.Hom.comp_apply _ _ _
      obtain ⟨w', hw'⟩ := hD'pre'.ge hx
      exact ⟨w', by rw [hmdef, Scheme.Hom.comp_apply, hw', hbeinvhom]⟩
  -- the closure of the inverse image of `T` lies in the range of the partial section
  have hclosedK : IsClosed (Set.range lamK) := by
    rw [← Set.image_univ]
    exact lamK.isClosedMap _ isClosed_univ
  have hTrangeK : K.blowupMap ⁻¹' T ⊆ Set.range lamK := by
    intro x hx
    have h1 : K.blowupMap x ∈ (K.support.compl : X.Opens) :=
      Set.disjoint_left.mp hKdisj (hTU hx)
    obtain ⟨t, ht⟩ := mem_range_strictTransformMap_of_mem_of_mem_range q K.blowupMap
      K.support.compl h1 (hMrange (hTM hx))
    have hsurj : Function.Surjective ⇑eK.hom := by
      have := (Scheme.homeoOfIso eK).surjective
      rwa [Scheme.coe_homeoOfIso] at this
    obtain ⟨t', rfl⟩ := hsurj t
    exact ⟨t', by rw [hlamKdef, Scheme.Hom.comp_apply]; exact ht⟩
  have hclosureA : closure (K.blowupMap ⁻¹' T) ⊆
      (al.hom ≫ D.blowupMap) ⁻¹' (A : Set B₁.I.blowup) := by
    have hg : (al.hom ≫ D.blowupMap) ≫ B₁.I.blowupMap = K.blowupMap := by
      rw [Category.assoc, hal]
    have hpre : K.blowupMap ⁻¹' T =
        (al.hom ≫ D.blowupMap) ⁻¹' (B₁.I.blowupMap ⁻¹' T) := by
      rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hg]
    rw [hpre]
    refine (Continuous.closure_preimage_subset
      (al.hom ≫ D.blowupMap).continuous _).trans (Set.preimage_mono ?_)
    exact (closure_mono (Set.preimage_mono hTimg)).trans hCTA
  have hclosure : closure (K.blowupMap ⁻¹' T) ⊆ Set.range (m ≫ lamK) := by
    intro y hy
    obtain ⟨y₀, rfl⟩ : y ∈ Set.range lamK := closure_minimal hTrangeK hclosedK hy
    have hyA : D.blowupMap (al.hom (lamK y₀)) ∈ (A : Set B₁.I.blowup) := by
      have := hclosureA hy
      rwa [Set.mem_preimage, Scheme.Hom.comp_apply] at this
    have hkey : al.hom (lamK y₀) = lamD (be.hom y₀) := by
      calc al.hom (lamK y₀) = (lamK ≫ al.hom) y₀ := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (be.hom ≫ lamD) y₀ := by rw [hlamKal]
        _ = lamD (be.hom y₀) := Scheme.Hom.comp_apply _ _ _
    rw [hkey] at hyA
    have hmem : be.hom y₀ ∈ Set.range hD' := by
      rw [hD'range, Set.mem_preimage, Scheme.Hom.comp_apply]
      exact hyA
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, ?_⟩
    have hbeinvhom : be.inv (be.hom y₀) = y₀ := by
      rw [← Scheme.Hom.comp_apply, be.hom_inv_id]
      rfl
    calc (m ≫ lamK) w = lamK (m w) := Scheme.Hom.comp_apply _ _ _
      _ = lamK (be.inv (hD' w)) := by rw [hmdef]; rfl
      _ = lamK (be.inv (be.hom y₀)) := by rw [hw]
      _ = lamK y₀ := by rw [hbeinvhom]
  -- Step 10: conclude.
  have hmst : (m ≫ eK.hom) ≫ st = m ≫ lamK := by rw [hlamKdef, Category.assoc]
  have : IsOpenImmersion ((m ≫ eK.hom) ≫ st) := by rw [hmst]; infer_instance
  refine ⟨⟨K, hKft, hKdisj⟩, ((m ≫ eK.hom) ≫ st).opensRange, ?_, ?_⟩
  · change closure (K.blowupMap ⁻¹' T) ⊆ Set.range ((m ≫ eK.hom) ≫ st)
    rw [hmst]
    exact hclosure
  · change IsIso (st ∣_ ((m ≫ eK.hom) ≫ st).opensRange)
    refine isIso_morphismRestrict_opensRange_of_range_eq st (m ≫ eK.hom) ?_
    have hsurj : Function.Surjective ⇑eK.hom := by
      have := (Scheme.homeoOfIso eK).surjective
      rwa [Scheme.coe_homeoOfIso] at this
    rw [hmst]
    ext t
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← Scheme.Hom.comp_apply, hmst]⟩
    · intro ht
      obtain ⟨t₀, rfl⟩ := hsurj t
      have : lamK t₀ ∈ Set.range (m ≫ lamK) := by
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hlamKdef] at ht
      obtain ⟨w, hw⟩ := hmrange.ge this
      exact ⟨w, by rw [hmdef] at hw ⊢; rw [Scheme.Hom.comp_apply, hw]⟩

/-- **The isomorphism-near-closure blow-up** `IsoBl_{U,T}(q)`: for a proper morphism
`q : Z ⟶ X` over a qcqs scheme `X` which is an isomorphism over an open neighbourhood `N` of a
piece `T ⊆ U` that is closed in the quasi-compact open `U`, a selected `U`-admissible blow-up of
`X` after which the strict transform of `q` is an isomorphism over a neighbourhood of the closure
of the inverse image of `T`. It is selected from
`AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure`, whose proof
performs the blueprint's construction: constructible separation of `T` from the complement of the
maximal isomorphism open, the separation blow-up, elimination of indeterminacy over the
separated region, extension of that blow-up and composition of the two blow-ups.
(blueprint: `def-nagata-isomorphism-near-closure`) -/
noncomputable def isoNearClosureBlowup {X Z : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) : IsAdmissible X U :=
  (exists_admissibleBlowup_isIso_strictTransformMap_near_closure hU q hTU hT hTN hN).choose

/-- **The isomorphism-near-closure blow-up does its job** (blueprint:
`lemma-nagata-isomorphism-near-closure`): after the blow-up `IsoBl_{U,T}(q)`, the strict
transform of `q` is an isomorphism over an open neighbourhood of the closure of the inverse
image of `T`. -/
theorem exists_isIso_strictTransformMap_isoNearClosureBlowup {X Z : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ N' : (isoNearClosureBlowup hU q hTU hT hTN hN).I.blowup.Opens,
      closure ((isoNearClosureBlowup hU q hTU hT hTN hN).I.blowupMap ⁻¹' T) ⊆
        (N' : Set (isoNearClosureBlowup hU q hTU hT hTN hN).I.blowup) ∧
      IsIso (strictTransformMap q (isoNearClosureBlowup hU q hTU hT hTN hN).I.blowupMap
        (isoNearClosureBlowup hU q hTU hT hTN hN).preservedOpen ∣_ N') :=
  (exists_admissibleBlowup_isIso_strictTransformMap_near_closure hU q hTU hT hTN hN).choose_spec

/-- **A proper open immersion with dense image is an isomorphism** (blueprint:
`lemma-nagata-proper-open-dense-iso`): if `q : Z ⟶ X` is proper and an open immersion, and its
image contains a scheme-theoretically dense quasi-compact open `D` of `X`, then `q` is an
isomorphism. The image of `q` is open, and closed because `q` is universally closed; it contains
the dense set `D`, hence is everything. -/
theorem isIso_of_isProper_of_isOpenImmersion {X Z : Scheme.{u}} (q : Z ⟶ X) [IsProper q]
    [IsOpenImmersion q] (D : X.Opens) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (hD : D ≤ q.opensRange) : IsIso q := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top q ?_
  have hclosed : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
  have hdense : closure (D : Set X) = Set.univ := by
    simpa using D.ι.denseRange.closure_range
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  have : closure (D : Set X) ⊆ Set.range q := hclosed.closure_subset_iff.mpr (by
    intro y hy; exact (hD hy : y ∈ q.opensRange))
  exact this (hdense ▸ Set.mem_univ x)

end AlgebraicGeometry
