/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.PartialSectionExtension
public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Elimination of indeterminacy

This file proves **elimination of indeterminacy** (Stacks Project Tag 081S; blueprint
chapter "Elimination of indeterminacy after Deligne and Conrad", `thm:081S`; proof order
item 30):

- `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`: if
  `q : Z ⟶ X` is separated, of finite type and an isomorphism over a quasi-compact open
  `U` of the qcqs scheme `X`, then after a `U`-admissible blow-up the strict transform of
  `q` is an open immersion.

This is the root of the modification layer: the transport of scheme-theoretic images
(`WeilConjectures.Compactification.ImageTransport`), common modifications
(`WeilConjectures.Compactification.CommonModification`), graph extensions
(`WeilConjectures.Compactification.GraphExtension`) and isomorphism near a boundary
closure (`WeilConjectures.Compactification.IsomorphismNearClosure`) are all consumers of
it, and the two-open compactification theorem (proof order items 43–48) consumes those.

## The route taken

The Stacks Project proves Tag 081S by Raynaud–Gruson flattening (Stacks Tags 0815 and
081R, together with 081P and 081L), but that chain — proof order items 25–29 — is *not*
the route taken here: it bottoms out in the dévissage sections of Stacks §§38.4–38.10,
which exist neither in Mathlib nor in the blueprint.

Tag 081S is formalized instead via **Conrad's Theorem 2.4 and Zariski's Main Theorem**,
written up in the blueprint chapter "Elimination of indeterminacy after Deligne and
Conrad" (proof order items 61–75). The statement of Conrad's Theorem 2.4 that this file
consumes is `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` of
`WeilConjectures.Blowup.PartialSectionExtension`, used here through its `U = V` corollary
`AlgebraicGeometry.exists_admissibleBlowup_extend_section` (Conrad's Remark 2.5). Both are
formalized: `exists_admissibleBlowup_extend_partialSection` is proved in
`WeilConjectures/Blowup/PartialSectionExtension.lean`, with the `U = V` corollary
`exists_admissibleBlowup_extend_section` in the same file. The external inputs of that
proof are ZMT, which is Mathlib's `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`,
and Stacks Tag 04II, formalized here as `exists_immersion_affineSpace_of_quasiAffine`
(`WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean`); see the route revision
note in `blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`.

The deduction of Tag 081S carried out here is: prepare a Cartier boundary
(`exists_admissibleBlowup_cartierBoundary`, Tag 080Y), so that `U` becomes
scheme-theoretically dense; extend the inverse of `q` over `U` to a section over an open
`W` of a second admissible blow-up, by Conrad's Remark 2.5; compose the two blow-ups
(`Scheme.IdealSheafData.exists_blowup_comp`, Tag 080B); and observe that the graph of the
extension, being closed and containing the scheme-theoretically dense `U`-graph, cuts out
the strict transform, which is therefore isomorphic to the open `W`.

Note that the two-open compactification theorem itself does not go through flattening
either way — it uses the boundary-separation route of
`WeilConjectures.Blowup.AdmissibleBlowup`.

The finite-type helper lemmas of the blueprint are already in Mathlib and are not
restated in this development: `lemma:nagata-proper-to-separated-target` is Mathlib's
`AlgebraicGeometry.IsProper.of_comp`, and the two halves of
`lemma:nagata-finite-type-to-separated-target` (hence also
`lemma:nagata-open-immersion-qc-over-separated-target`) are Mathlib's
`AlgebraicGeometry.locallyOfFiniteType_of_comp` and
`AlgebraicGeometry.QuasiCompact.of_comp` (the latter only needs the second leg
quasi-separated, which separatedness supplies).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Elimination of indeterminacy** (Stacks Project Tag 081S; blueprint:
`def:nagata-elimination-indeterminacy`, `lemma:nagata-elimination-indeterminacy`;
proof order item 30).

The proof follows the Conrad/Zariski's-Main-Theorem route: prepare a Cartier boundary
(`exists_admissibleBlowup_cartierBoundary`, Stacks Project Tag 080Y) so that `U` becomes
scheme-theoretically dense, extend the inverse of `q` over `U` to a section over an open
`W` of a second admissible blow-up (`exists_admissibleBlowup_extend_section`, Conrad's
Remark 2.5), compose the two blow-ups (`Scheme.IdealSheafData.exists_blowup_comp`, Stacks
Project Tag 080B, whose support formula shows that the composite centre is still supported
exactly on the complement of `U`), and identify the strict transform with `W`: the graph
of the extension is closed and contains the scheme-theoretically dense `U`-graph, so it
cuts out the strict transform. -/
theorem exists_admissibleBlowup_isOpenImmersion_strictTransformMap
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (q : Z ⟶ X)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hq : IsIso (q ∣_ U)) :
    ∃ B : IsAdmissible X U,
      IsOpenImmersion (strictTransformMap q B.I.blowupMap B.preservedOpen) := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated q
  -- **Step 1: boundary preparation** (Stacks Project Tag 080Y). After blowing up a
  -- finite-type ideal whose support is exactly the boundary, `U` is scheme-theoretically
  -- dense. The centre is taken here rather than through
  -- `exists_admissibleBlowup_cartierBoundary`, because step 3 needs its support to be
  -- exactly the complement of `U`.
  obtain ⟨I₁, hI₁ft, hI₁supp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl U hU
  have hI₁compl : I₁.support.compl = U := by
    apply TopologicalSpace.Opens.ext
    change (I₁.support : Set X)ᶜ = (U : Set X)
    rw [hI₁supp, compl_compl]
  have hdisj₁ : Disjoint (U : Set X) (I₁.support : Set X) := by
    rw [hI₁supp]; exact disjoint_compl_right
  set π₁ : I₁.blowup ⟶ X := I₁.blowupMap with hπ₁def
  have hproper₁ : IsProper π₁ := IsAdmissible.isProper_blowupMap ⟨I₁, hI₁ft, hdisj₁⟩
  have : QuasiCompact π₁ := inferInstance
  have : IsSeparated π₁ := inferInstance
  have : CompactSpace I₁.blowup := QuasiCompact.compactSpace_of_compactSpace π₁
  have : QuasiSeparatedSpace I₁.blowup := quasiSeparatedSpace_of_quasiSeparated π₁
  have hU₁ : IsCompact ((π₁ ⁻¹ᵁ U : I₁.blowup.Opens) : Set I₁.blowup) :=
    QuasiCompact.isCompact_preimage (f := π₁) _ U.isOpen hU
  have hstd₁ : IsSchemeTheoreticallyDominant (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι := by
    have h := I₁.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    rwa [hI₁compl] at h
  have : CompactSpace (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).toScheme := isCompact_iff_compactSpace.mp hU₁
  have : QuasiCompact (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι := inferInstance
  have hdense₁ : Dense ((π₁ ⁻¹ᵁ U : I₁.blowup.Opens) : Set I₁.blowup) := by
    have h := Scheme.Hom.denseRange (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι
    rwa [DenseRange, Scheme.Opens.range_ι] at h
  -- **Step 2: Conrad's Remark 2.5** applied to the base change of `q` to the blow-up.
  set p : pullback q π₁ ⟶ I₁.blowup := pullback.snd q π₁ with hpdef
  have : IsSeparated p := MorphismProperty.pullback_snd _ _ ‹_›
  have : LocallyOfFiniteType p := MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiCompact p := MorphismProperty.pullback_snd _ _ ‹_›
  have : CompactSpace ↥(pullback q π₁) := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace ↥(pullback q π₁) := quasiSeparatedSpace_of_quasiSeparated p
  set s : U.toScheme ⟶ Z := inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι with hsdef
  have hs : s ≫ q = U.ι := by
    rw [hsdef, Category.assoc, ← morphismRestrict_ι q U, IsIso.inv_hom_id_assoc]
  have hcond₁ : ((π₁ ∣_ U) ≫ s) ≫ q = (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι ≫ π₁ := by
    rw [Category.assoc, hs, morphismRestrict_ι]
  set f₁ : (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).toScheme ⟶ pullback q π₁ :=
    pullback.lift ((π₁ ∣_ U) ≫ s) (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι hcond₁ with hf₁def
  have hf₁snd : f₁ ≫ p = (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι := pullback.lift_snd _ _ _
  have hf₁fst : f₁ ≫ pullback.fst q π₁ = (π₁ ∣_ U) ≫ s := pullback.lift_fst _ _ _
  obtain ⟨B₂, W, hUW, g, hg, hext, hclosed⟩ :=
    exists_admissibleBlowup_extend_section hU₁ hdense₁ f₁ hf₁snd
  set π₂ : B₂.I.blowup ⟶ I₁.blowup := B₂.I.blowupMap with hπ₂def
  -- **Step 3: compose the two blow-ups** (Stacks Project Tag 080B). The support formula
  -- of the composite centre `K` gives `supp K = Uᶜ ∪ π₁(supp B₂.I) = Uᶜ`, so `K` is a
  -- `U`-admissible centre whose preserved open is exactly `U`.
  obtain ⟨K, hKft, hKsupp, e, he⟩ :=
    Scheme.IdealSheafData.exists_blowup_comp I₁ hI₁ft B₂.I B₂.finiteType
  have hdisjK : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hxI | ⟨x', hx', hx'eq⟩
    · exact Set.disjoint_left.mp hdisj₁ hxU hxI
    · refine Set.disjoint_left.mp B₂.disjoint_support ?_ hx'
      have hx'U : π₁ x' ∈ U := by rw [hx'eq]; exact hxU
      exact hx'U
  have hKcompl : K.support.compl = U := by
    apply TopologicalSpace.Opens.ext
    change (K.support : Set X)ᶜ = (U : Set X)
    have hsub : (U : Set X)ᶜ ⊆ (K.support : Set X) := by
      rw [hKsupp, ← hI₁supp]; exact Set.subset_union_left
    have hsub' : (K.support : Set X) ⊆ (U : Set X)ᶜ := Set.disjoint_left.mp hdisjK.symm
    rw [subset_antisymm hsub' hsub, compl_compl]
  refine ⟨⟨K, hKft, hdisjK⟩, ?_⟩
  change IsOpenImmersion (strictTransformMap q K.blowupMap K.support.compl)
  rw [hKcompl]
  set π : K.blowup ⟶ X := K.blowupMap with hπdef
  have hproperK : IsProper π := IsAdmissible.isProper_blowupMap ⟨K, hKft, hdisjK⟩
  have : QuasiCompact π := inferInstance
  have : IsSeparated π := inferInstance
  have : CompactSpace K.blowup := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace K.blowup := quasiSeparatedSpace_of_quasiSeparated π
  have hisoπ : IsIso (π ∣_ U) := IsAdmissible.isIso_blowupMap_restrict ⟨K, hKft, hdisjK⟩
  -- `U` is scheme-theoretically dense in the composite blow-up
  have hstdK : IsSchemeTheoreticallyDominant (π ⁻¹ᵁ U : K.blowup.Opens).ι := by
    have h := K.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    rwa [hKcompl] at h
  have hcptV : IsCompact ((π ⁻¹ᵁ U : K.blowup.Opens) : Set K.blowup) :=
    QuasiCompact.isCompact_preimage (f := π) _ U.isOpen hU
  have : CompactSpace (π ⁻¹ᵁ U : K.blowup.Opens).toScheme := isCompact_iff_compactSpace.mp hcptV
  have : QuasiCompact (π ⁻¹ᵁ U : K.blowup.Opens).ι := inferInstance
  -- the preimage of `U` in the composite blow-up lands in the transported open `W`
  have hmem : ∀ y : K.blowup, y ∈ (π ⁻¹ᵁ U : K.blowup.Opens) →
      e.hom y ∈ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens) := by
    intro y hy
    change π₁ (π₂ (e.hom y)) ∈ U
    have h1 : π y = π₁ (π₂ (e.hom y)) := by
      conv_lhs => rw [← he]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact h1 ▸ hy
  have hV₀ : (π ⁻¹ᵁ U : K.blowup.Opens) ≤ e.hom ⁻¹ᵁ W := fun y hy => hUW (hmem y hy)
  -- the open locus over `U` is the preimage of `U`, since `q` and `π` are isomorphisms there
  set ρ : (strictTransformOpen q π U).toScheme ⟶ (π ⁻¹ᵁ U : K.blowup.Opens).toScheme :=
    pullback.snd q π ∣_ (π ⁻¹ᵁ U) with hρdef
  have hρι : ρ ≫ (π ⁻¹ᵁ U : K.blowup.Opens).ι =
      (strictTransformOpen q π U).ι ≫ pullback.snd q π := morphismRestrict_ι _ _
  set ω : (strictTransformOpen q π U).toScheme ≅ (q ⁻¹ᵁ U).toScheme :=
    (isPullback_strictTransformOpen q π U).isoIsPullback _ _
      (isPullback_morphismRestrict q U).flip with hωdef
  have hωfst : ω.hom ≫ (q ⁻¹ᵁ U).ι = (strictTransformOpen q π U).ι ≫ pullback.fst q π := by
    rw [hωdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hωsnd : ω.hom ≫ (q ∣_ U) = ρ ≫ (π ∣_ U) := by
    rw [hωdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hρiso : IsIso ρ := by
    have h1 : ρ = ω.hom ≫ (q ∣_ U) ≫ inv (π ∣_ U) := by
      rw [← Category.assoc, hωsnd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [h1]; infer_instance
  -- the preimage of `U`, transported into the blow-up of the second centre
  have hrangeν : Set.range ((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) ⊆
      Set.range (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine hmem _ ?_
    have h := Set.mem_range_self (f := ⇑(π ⁻¹ᵁ U : K.blowup.Opens).ι) y
    rwa [Scheme.Opens.range_ι] at h
  set ν : (π ⁻¹ᵁ U : K.blowup.Opens).toScheme ⟶ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).toScheme :=
    IsOpenImmersion.lift (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι
      ((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) hrangeν with hνdef
  have hνι : ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι =
      (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom := IsOpenImmersion.lift_fac _ _ _
  have hνπ : ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U) = π ∣_ U := by
    rw [← cancel_mono U.ι]
    calc (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U)) ≫ U.ι
        = ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U) ≫ U.ι := by simp only [Category.assoc]
      _ = ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι ≫ π₁ := by
          rw [morphismRestrict_ι]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ⁻¹ᵁ U : I₁.blowup.Opens).ι) ≫ π₁ := by
          simp only [Category.assoc]
      _ = (ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι ≫ π₂) ≫ π₁ := by
          rw [morphismRestrict_ι]
      _ = ((ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι) ≫ π₂) ≫ π₁ := by
          simp only [Category.assoc]
      _ = (((π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom) ≫ π₂) ≫ π₁ := by rw [hνι]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom ≫ π₂ ≫ π₁ := by simp only [Category.assoc]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ π := by rw [he]
      _ = (π ∣_ U) ≫ U.ι := by rw [morphismRestrict_ι]
  have hνW : K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) = ν ≫ B₂.I.blowup.homOfLE hUW := by
    rw [← cancel_mono W.ι]
    calc (K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W)) ≫ W.ι
        = K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ W.ι := by simp only [Category.assoc]
      _ = K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι ≫ e.hom := by rw [morphismRestrict_ι]
      _ = (K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι) ≫ e.hom := by simp only [Category.assoc]
      _ = (π ⁻¹ᵁ U : K.blowup.Opens).ι ≫ e.hom := by rw [Scheme.homOfLE_ι]
      _ = ν ≫ (π₂ ⁻¹ᵁ (π₁ ⁻¹ᵁ U) : B₂.I.blowup.Opens).ι := by rw [hνι]
      _ = ν ≫ B₂.I.blowup.homOfLE hUW ≫ W.ι := by rw [Scheme.homOfLE_ι]
      _ = (ν ≫ B₂.I.blowup.homOfLE hUW) ≫ W.ι := by simp only [Category.assoc]
  have hgU : K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ = (π ∣_ U) ≫ s := by
    calc K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁
        = (K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W)) ≫ g ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = (ν ≫ B₂.I.blowup.homOfLE hUW) ≫ g ≫ pullback.fst q π₁ := by rw [hνW]
      _ = ν ≫ (B₂.I.blowup.homOfLE hUW ≫ g) ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = ν ≫ ((π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) ≫ pullback.fst q π₁ := by rw [hext]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U))) ≫ f₁ ≫ pullback.fst q π₁ := by simp only [Category.assoc]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U))) ≫ (π₁ ∣_ U) ≫ s := by rw [hf₁fst]
      _ = (ν ≫ (π₂ ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ∣_ U)) ≫ s := by simp only [Category.assoc]
      _ = (π ∣_ U) ≫ s := by rw [hνπ]
  -- the comparison of the two fibre products
  have hbig : IsPullback (pullback.fst p π₂ ≫ pullback.fst q π₁)
      (pullback.snd p π₂ ≫ e.inv) q π := by
    have h0 : IsPullback (𝟙 (pullback p π₂)) (pullback.snd p π₂ ≫ e.inv)
        (pullback.snd p π₂) e.hom := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h12 := (IsPullback.of_hasPullback p π₂).paste_horiz (IsPullback.of_hasPullback q π₁)
    have h := h0.paste_horiz h12
    rwa [Category.id_comp, he] at h
  set E : pullback p π₂ ≅ pullback q π :=
    hbig.isoIsPullback _ _ (IsPullback.of_hasPullback q π) with hEdef
  have hEfst : E.hom ≫ pullback.fst q π = pullback.fst p π₂ ≫ pullback.fst q π₁ := by
    rw [hEdef]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hEsnd : E.hom ≫ pullback.snd q π = pullback.snd p π₂ ≫ e.inv := by
    rw [hEdef]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _
  -- the graph of the extension is a closed immersion
  set Γ : W.toScheme ⟶ pullback p π₂ := pullback.lift g W.ι hg with hΓdef
  have hΓsnd : Γ ≫ pullback.snd p π₂ = W.ι := pullback.lift_snd _ _ _
  have hΓfst : Γ ≫ pullback.fst p π₂ = g := pullback.lift_fst _ _ _
  have hΓimm : IsImmersion (Γ ≫ pullback.snd p π₂) := by rw [hΓsnd]; infer_instance
  have : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd p π₂)
  have hΓci : IsClosedImmersion Γ := IsClosedImmersion.of_isPreimmersion Γ hclosed
  set ψ : (e.hom ⁻¹ᵁ W).toScheme ⟶ pullback q π := (e.hom ∣_ W) ≫ Γ ≫ E.hom with hψdef
  have hψci : IsClosedImmersion ψ := by rw [hψdef]; infer_instance
  have hψsnd : ψ ≫ pullback.snd q π = (e.hom ⁻¹ᵁ W).ι := by
    calc ψ ≫ pullback.snd q π
        = (e.hom ∣_ W) ≫ Γ ≫ E.hom ≫ pullback.snd q π := by
          rw [hψdef]; simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ Γ ≫ pullback.snd p π₂ ≫ e.inv := by rw [hEsnd]
      _ = (e.hom ∣_ W) ≫ (Γ ≫ pullback.snd p π₂) ≫ e.inv := by simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ W.ι ≫ e.inv := by rw [hΓsnd]
      _ = ((e.hom ∣_ W) ≫ W.ι) ≫ e.inv := by simp only [Category.assoc]
      _ = ((e.hom ⁻¹ᵁ W).ι ≫ e.hom) ≫ e.inv := by rw [morphismRestrict_ι]
      _ = (e.hom ⁻¹ᵁ W).ι := by simp
  have hψfst : ψ ≫ pullback.fst q π = (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by
    calc ψ ≫ pullback.fst q π
        = (e.hom ∣_ W) ≫ Γ ≫ E.hom ≫ pullback.fst q π := by
          rw [hψdef]; simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ Γ ≫ pullback.fst p π₂ ≫ pullback.fst q π₁ := by rw [hEfst]
      _ = (e.hom ∣_ W) ≫ (Γ ≫ pullback.fst p π₂) ≫ pullback.fst q π₁ := by
          simp only [Category.assoc]
      _ = (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by rw [hΓfst]
  -- the open locus over `U` sits scheme-theoretically densely inside the graph
  set θ : (strictTransformOpen q π U).toScheme ⟶ (e.hom ⁻¹ᵁ W).toScheme :=
    ρ ≫ K.blowup.homOfLE hV₀ with hθdef
  have hstdLE : IsSchemeTheoreticallyDominant (K.blowup.homOfLE hV₀) :=
    IsSchemeTheoreticallyDominant.homOfLE hV₀
  have hθstd : IsSchemeTheoreticallyDominant θ := by rw [hθdef]; infer_instance
  have hθW : θ ≫ (e.hom ⁻¹ᵁ W).ι = (strictTransformOpen q π U).ι ≫ pullback.snd q π := by
    calc θ ≫ (e.hom ⁻¹ᵁ W).ι
        = ρ ≫ K.blowup.homOfLE hV₀ ≫ (e.hom ⁻¹ᵁ W).ι := by
          rw [hθdef]; simp only [Category.assoc]
      _ = ρ ≫ (π ⁻¹ᵁ U : K.blowup.Opens).ι := by rw [Scheme.homOfLE_ι]
      _ = (strictTransformOpen q π U).ι ≫ pullback.snd q π := hρι
  have hθfst : θ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ =
      (strictTransformOpen q π U).ι ≫ pullback.fst q π := by
    calc θ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁
        = ρ ≫ K.blowup.homOfLE hV₀ ≫ (e.hom ∣_ W) ≫ g ≫ pullback.fst q π₁ := by
          rw [hθdef]; simp only [Category.assoc]
      _ = ρ ≫ (π ∣_ U) ≫ s := by rw [hgU]
      _ = (ρ ≫ (π ∣_ U)) ≫ s := by simp only [Category.assoc]
      _ = (ω.hom ≫ (q ∣_ U)) ≫ s := by rw [← hωsnd]
      _ = ω.hom ≫ (q ∣_ U) ≫ inv (q ∣_ U) ≫ (q ⁻¹ᵁ U).ι := by
          rw [hsdef]; simp only [Category.assoc]
      _ = ω.hom ≫ (q ⁻¹ᵁ U).ι := by rw [IsIso.hom_inv_id_assoc]
      _ = (strictTransformOpen q π U).ι ≫ pullback.fst q π := hωfst
  have hθψ : θ ≫ ψ = (strictTransformOpen q π U).ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψfst]; exact hθfst
    · rw [Category.assoc, hψsnd]; exact hθW
  -- the strict transform is cut out by the graph, hence isomorphic to the open `W`
  have hker : (strictTransformι q π U).ker = ψ.ker := by
    rw [ker_strictTransformι, ← hθψ]
    exact Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant θ ψ
  set α := IsClosedImmersion.lift (strictTransformι q π U) ψ hker.le with hαdef
  have hαiso : IsIso α := IsClosedImmersion.isIso_lift (strictTransformι q π U) ψ hker
  have hα : α ≫ strictTransformι q π U = ψ := IsClosedImmersion.lift_fac _ _ _
  have hfinal : α ≫ strictTransformMap q π U = (e.hom ⁻¹ᵁ W).ι := by
    rw [strictTransformMap, ← Category.assoc, hα, hψsnd]
  have hrw : strictTransformMap q π U = inv α ≫ (e.hom ⁻¹ᵁ W).ι := by
    rw [← hfinal, IsIso.inv_hom_id_assoc]
  rw [hrw]
  infer_instance

/-- **The elimination-of-indeterminacy blow-up** `X^el(q, U) ⟶ X`: for a separated morphism
`q : Z ⟶ X` of finite type over a qcqs scheme `X` which is an isomorphism over a quasi-compact
open `U`, a selected `U`-admissible blow-up of `X` along which the strict transform
`Z^el(q, U) ⟶ X^el(q, U)` of `q` is an open immersion. It is selected from
`AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`, whose proof
performs the blueprint's three steps: the boundary preparation `X₁ = Bl_{I₀} X` making `U`
scheme-theoretically dense, Conrad's extension of the induced quasi-domination over a second
admissible blow-up of `X₁`, and the composition of the two blow-ups into a single `U`-admissible
blow-up of `X`. (blueprint: `def-nagata-elimination-indeterminacy`) -/
noncomputable def eliminationBlowup {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (q : Z ⟶ X)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] (hq : IsIso (q ∣_ U)) :
    IsAdmissible X U :=
  (exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU q hq).choose

/-- **Elimination of indeterminacy for the constructed blow-up** (Stacks Project Tag 081S;
blueprint: `lemma-nagata-elimination-indeterminacy`): the strict transform of `q` along
`AlgebraicGeometry.eliminationBlowup` is an open immersion. -/
theorem isOpenImmersion_strictTransformMap_eliminationBlowup {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) {Z : Scheme.{u}}
    (q : Z ⟶ X) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] (hq : IsIso (q ∣_ U)) :
    IsOpenImmersion (strictTransformMap q (eliminationBlowup hU q hq).I.blowupMap
      (eliminationBlowup hU q hq).preservedOpen) :=
  (exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU q hq).choose_spec

/-! ### Axiom census

Elimination of indeterminacy is unconditional: the check below is run by the build, so a
`sorry` reappearing anywhere beneath Stacks Project Tag 081S breaks compilation rather than
going unnoticed. -/

/--
info: 'AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap

end AlgebraicGeometry
