/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Blowup.PartialSectionExtension
public import WeilConjectures.Compactification.StrictTransformBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import WeilConjectures.Mathlib.Topology.Spectral.Prespectral

/-!

# Elimination of indeterminacy, common modifications and graph extension

This file records the modification steps of the proof of Nagata's compactification
theorem, following the blueprint chapter "Nagata compactification", sections
"Boundary preparation" and "Common modifications and graph extension"
(proof order items 30–33):

- `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`:
  **elimination of indeterminacy** (Stacks Project Tag 081S; blueprint
  `lemma:nagata-elimination-indeterminacy`): if `q : Z ⟶ X` is separated, of finite
  type and an isomorphism over a quasi-compact open `U` of the qcqs scheme `X`, then
  after a `U`-admissible blow-up the strict transform of `q` is an open immersion;
- `AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup`:
  **transport of scheme-theoretic images through admissible blow-ups** (Stacks
  Project Tag 0F3Y; blueprint `lemma:nagata-scheme-image-strict-transform`): the
  scheme-theoretic image of a lift along a `U`-admissible blow-up is the strict
  transform of the scheme-theoretic image;
- `AlgebraicGeometry.CommonModification` and
  `AlgebraicGeometry.nonempty_commonModification`: **common modification of two models**
  (Stacks Project Tag 0F3X; blueprint `def:nagata-common-modification`,
  `lemma:nagata-common-modification`): two separated finite-type models of a common
  open `U` admit `U`-admissible blow-ups which glue along a common copy of the
  modified `U`-locus to a separated finite-type model;
- `AlgebraicGeometry.Compactification.nonempty_properExtension`: **graph extension**
  (Stacks Project Tag 0F3Z; blueprint `def:nagata-graph-extension`,
  `lemma:nagata-graph-extension`): a compactification of a quasi-compact open
  `V ⊆ U` extends, after a `V`-admissible blow-up of the compactification, to a
  proper morphism `V^gr ⟶ U` restricting to the identity on `V`;
- `AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure`:
  **isomorphism near a boundary closure** (Stacks Project Tag 0F3W; blueprint
  `def:nagata-isomorphism-near-closure`, `lemma:nagata-isomorphism-near-closure`): a
  proper morphism which is an isomorphism over a neighbourhood of a closed piece `T`
  of `U` acquires, after a `U`-admissible blow-up, a strict transform which is an
  isomorphism over a neighbourhood of the closure of `T`.

The extension step of the common-modification construction is recorded separately as
`AlgebraicGeometry.IsAdmissible.exists_isOpenImmersion_blowup`: a further finite-type
blow-up of the strict transform of a morphism `p` along a `U`-admissible blow-up sits, as
an open subscheme, inside a single `U`-admissible blow-up of the base. This combines
Stacks Project Tag 080E (the strict transform is the blow-up of the pulled-back centre)
with the extension and composition of admissible centres.

The finite-type helper lemmas of the blueprint are already in Mathlib and are not
restated here: `lemma:nagata-proper-to-separated-target` is Mathlib's
`AlgebraicGeometry.IsProper.of_comp`, and the two halves of
`lemma:nagata-finite-type-to-separated-target` (hence also
`lemma:nagata-open-immersion-qc-over-separated-target`) are Mathlib's
`AlgebraicGeometry.locallyOfFiniteType_of_comp` and
`AlgebraicGeometry.QuasiCompact.of_comp` (the latter only needs the second leg
quasi-separated, which separatedness supplies).

## Dependency structure

`exists_admissibleBlowup_isOpenImmersion_strictTransformMap` (Tag 081S) is the root of
this file: `Scheme.Hom.ker_lift_admissibleBlowup` (0F3Y),
`nonempty_commonModification` (0F3X), `Compactification.nonempty_properExtension` (0F3Z)
and `exists_admissibleBlowup_isIso_strictTransformMap_near_closure` (0F3W) are all
consumers of it, and the two-open compactification theorem (proof order items 43–48)
consumes those. The Stacks Project proves Tag 081S by Raynaud–Gruson flattening
(Stacks Tags 0815 and 081R, together with 081P and 081L), but that chain — proof order
items 25–29 — is *not* the route taken here: it bottoms out in the dévissage sections
of Stacks §§38.4–38.10, which exist neither in Mathlib nor in the blueprint.

Tag 081S is formalized instead via **Conrad's Theorem 2.4 and Zariski's Main
Theorem**, written up in the blueprint chapter "Elimination of indeterminacy after
Deligne and Conrad" (`blueprint/src/version/detailed/nagata/nagata_new.tex`, proof
order items 61–75). The statement of Conrad's Theorem 2.4 that this file consumes is
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` of
`WeilConjectures.Blowup.PartialSectionExtension`, used here through its `U = V`
corollary `AlgebraicGeometry.exists_admissibleBlowup_extend_section` (Conrad's Remark
2.5); it is the single remaining primitive obligation of the modification layer. The
external inputs of its proof are available — ZMT is Mathlib's
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, and Stacks Tag 04II is already
formalized here as `exists_immersion_affineSpace_of_quasiAffine`
(`WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean`) — but that proof is not
formalized yet; see the route revision note in
`blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`.

The deduction of Tag 081S carried out here is: prepare a Cartier boundary
(`exists_admissibleBlowup_cartierBoundary`, Tag 080Y), so that `U` becomes
scheme-theoretically dense; extend the inverse of `q` over `U` to a section over an
open `W` of a second admissible blow-up, by Conrad's Remark 2.5; compose the two
blow-ups (`Scheme.IdealSheafData.exists_blowup_comp`, Tag 080B); and observe that the
graph of the extension, being closed and containing the scheme-theoretically dense
`U`-graph, cuts out the strict transform, which is therefore isomorphic to the open `W`.

Note that the two-open compactification theorem itself does not go through flattening
either way — it uses the boundary-separation route of
`WeilConjectures.Blowup.AdmissibleBlowup`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Elimination of indeterminacy** (Stacks Project Tag 081S): let `X` be a qcqs
scheme, `U ⊆ X` a quasi-compact open and `q : Z ⟶ X` separated, of finite type and an
isomorphism over `U`. Then there is a `U`-admissible blow-up `X' ⟶ X` such that the
strict transform `Z' ⟶ X'` of `q` is an open immersion.

The proof follows the Conrad/Zariski's-Main-Theorem route: prepare a Cartier boundary
(`exists_admissibleBlowup_cartierBoundary`, Stacks Project Tag 080Y) so that `U` becomes
scheme-theoretically dense, extend the inverse of `q` over `U` to a section over an open
`W` of a second admissible blow-up (`exists_admissibleBlowup_extend_section`, Conrad's
Remark 2.5), compose the two blow-ups (`Scheme.IdealSheafData.exists_blowup_comp`, Stacks
Project Tag 080B, whose support formula shows that the composite centre is still supported
exactly on the complement of `U`), and identify the strict transform with `W`: the graph
of the extension is closed and contains the scheme-theoretically dense `U`-graph, so it
cuts out the strict transform.

(Blueprint: `def:nagata-elimination-indeterminacy`,
`lemma:nagata-elimination-indeterminacy`; proof order item 30.) -/
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

section ImageTransport

variable {S X Y V : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y):
let `h : V ⟶ X ×_S Y` be quasi-compact whose first projection factors through a
quasi-compact open `U ⊆ X`, and let `B` be a `U`-admissible blow-up of `X`. For every
lift `h' : V ⟶ X' ×_S Y` of `h` along the base-changed blow-up `X' ×_S Y ⟶ X ×_S Y`
(such a lift exists because the blow-up is an isomorphism over `U`), the
scheme-theoretic image of `h'` is the strict transform of the scheme-theoretic image
of `h`, as closed subschemes of `X' ×_S Y`.

The statement is in kernel ideal sheaf form: both closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions. The Stacks Project and
the blueprint also assume `h` quasi-separated; Mathlib's kernel ideal sheaf theory only
needs quasi-compactness, so that hypothesis is dropped here.

**Hypotheses.** The right-hand side is a strict transform, so the theorem carries the
standing quasi-compactness assumption of
`WeilConjectures.Compactification.StrictTransform`: the inclusion of the open locus
over the preserved open must be a quasi-compact morphism, which is exactly what every
comparison lemma about the strict transform requires. It is not implied by the
remaining hypotheses — nothing here makes `U`, `B.preservedOpen` or `X` quasi-compact —
and is discharged from finiteness data by
`AlgebraicGeometry.quasiCompact_strictTransformOpen_ι_of_isCompact`. (The
specialization `AlgebraicGeometry.quasiCompact_strictTransformOpen_ι` does *not* apply:
it is stated for a blow-up map of an ideal sheaf, not for the base-changed blow-up
occurring here.)
(Blueprint: `lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31.) -/
theorem Scheme.Hom.ker_lift_admissibleBlowup
    {U : X.Opens} (B : IsAdmissible X U)
    (h : V ⟶ pullback x y) [QuasiCompact h]
    (hfac : Set.range (h ≫ pullback.fst x y) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.I.blowupMap ≫ x) y)
    (hlift : h' ≫ partialSectionOpenι x y B.I.blowupMap = h)
    [QuasiCompact (strictTransformOpen h.imageι (partialSectionOpenι x y B.I.blowupMap)
      (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ι] :
    h'.ker =
      (strictTransformMap h.imageι (partialSectionOpenι x y B.I.blowupMap)
        (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ker := by
  set ρ := partialSectionOpenι x y B.I.blowupMap
  set W : (pullback x y).Opens := pullback.fst x y ⁻¹ᵁ B.preservedOpen
  set L := strictTransformOpen h.imageι ρ W
  -- `h` lands over the preserved open, because it lands over `U ≤ B.preservedOpen`.
  have hrange : Set.range h ⊆ (W : Set ↥(pullback x y)) := by
    rintro _ ⟨v, rfl⟩
    exact B.le_preservedOpen (by simpa [Scheme.Hom.comp_apply] using hfac ⟨v, rfl⟩)
  -- The blow-up is an isomorphism over its own preserved open, ...
  have : IsIso (B.I.blowupMap ∣_ B.preservedOpen) :=
    B.I.isIso_blowupMap_restrict_support_compl
  -- ... hence so is its base change, over the preimage of the preserved open.
  have : IsIso (ρ ∣_ W) :=
    isIso_partialSectionOpenι_restrict x y B.I.blowupMap B.preservedOpen
  -- So the open locus is the restriction of `SIm(h)` over the preserved open.
  have hPB := isPullback_strictTransformOpen h.imageι ρ W
  -- The lift of `h` to `SIm(h) ×_(X ×_S Y) (X' ×_S Y)`.
  have hcond : h.toImage ≫ h.imageι = h' ≫ ρ := by
    rw [Scheme.Hom.toImage_imageι, hlift]
  set k := pullback.lift h.toImage h' hcond
  have hkfst : k ≫ pullback.fst h.imageι ρ = h.toImage := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd h.imageι ρ = h' := pullback.lift_snd _ _ _
  -- It lands in the open locus, again because `h` lands over the preserved open.
  have hkrange : Set.range (k ≫ pullback.fst h.imageι ρ ≫ h.imageι) ⊆
      (W : Set ↥(pullback x y)) := by
    rw [← Category.assoc, hkfst, Scheme.Hom.toImage_imageι]
    exact hrange
  set m := strictTransformOpenLift h.imageι ρ W k hkrange
  have hmfac : m ≫ L.ι = k := strictTransformOpenLift_ι h.imageι ρ W k hkrange
  -- The projection of the open locus to `SIm(h)` is a base change of the open immersion
  -- `W ⟶ X ×_S Y`, so `V` sits inside the open locus as a flat base change of
  -- `V ⟶ SIm(h)`, and scheme-theoretic dominance descends.
  have : IsOpenImmersion (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsOpenImmersion.of_isPullback hPB.flip inferInstance
  have hsq : IsPullback (𝟙 V) m h.toImage (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsPullback.of_horiz_isIso_mono
      ⟨by rw [Category.id_comp, ← Category.assoc, hmfac, hkfst]⟩
  have : IsSchemeTheoreticallyDominant m := .of_isPullback hsq
  calc h'.ker = (m ≫ (L.ι ≫ pullback.snd h.imageι ρ)).ker := by
        rw [← Category.assoc, hmfac, hksnd]
    _ = (L.ι ≫ pullback.snd h.imageι ρ).ker :=
        Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _
    _ = _ := (ker_strictTransformMap h.imageι ρ W).symm

end ImageTransport

section CommonModification

variable {S U X₁ X₂ : Scheme.{u}}

/-- The data of a **common modification** of two separated finite-type models `X₁`,
`X₂` of a common open `U` over `S` (Stacks Project Tag 0F3X): admissible blow-ups
`X'ᵢ ⟶ Xᵢ`, open immersions of both `X'ᵢ` into a glued scheme `W`, agreeing lifted
copies of `U`, such that the two opens cover `W` and `W` is separated and of finite
type over `S`.
(Blueprint: `def:nagata-common-modification`.) -/
structure CommonModification (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] where
  /-- The `U`-admissible blow-up of the first model. -/
  B₁ : IsAdmissible X₁ j₁.opensRange
  /-- The `U`-admissible blow-up of the second model. -/
  B₂ : IsAdmissible X₂ j₂.opensRange
  /-- The glued common modification. -/
  W : Scheme.{u}
  /-- The structure morphism of the common modification. -/
  w : W ⟶ S
  /-- The open immersion of the first modified model into the glued scheme. -/
  k₁ : B₁.I.blowup ⟶ W
  /-- The open immersion of the second modified model into the glued scheme. -/
  k₂ : B₂.I.blowup ⟶ W
  /-- The first modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₁ : IsOpenImmersion k₁
  /-- The second modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₂ : IsOpenImmersion k₂
  /-- The first open immersion lies over `S`. -/
  k₁_w : k₁ ≫ w = B₁.I.blowupMap ≫ s₁
  /-- The second open immersion lies over `S`. -/
  k₂_w : k₂ ≫ w = B₂.I.blowupMap ≫ s₂
  /-- The lift of `U` into the first modified model. -/
  u₁ : U ⟶ B₁.I.blowup
  /-- The lift of `U` into the second modified model. -/
  u₂ : U ⟶ B₂.I.blowup
  /-- The first lift of `U` lies over the given open immersion `j₁`. -/
  u₁_blowupMap : u₁ ≫ B₁.I.blowupMap = j₁
  /-- The second lift of `U` lies over the given open immersion `j₂`. -/
  u₂_blowupMap : u₂ ≫ B₂.I.blowupMap = j₂
  /-- The two copies of `U` in the glued scheme agree. -/
  u_glue : u₁ ≫ k₁ = u₂ ≫ k₂
  /-- The two modified models cover the glued scheme. -/
  cover : Set.range k₁ ∪ Set.range k₂ = Set.univ
  /-- The glued scheme is separated over `S`. -/
  isSeparated_w : IsSeparated w
  /-- The glued scheme is locally of finite type over `S`. -/
  locallyOfFiniteType_w : LocallyOfFiniteType w
  /-- The glued scheme is quasi-compact over `S`. -/
  quasiCompact_w : QuasiCompact w

attribute [instance] CommonModification.isOpenImmersion_k₁
  CommonModification.isOpenImmersion_k₂ CommonModification.isSeparated_w
  CommonModification.locallyOfFiniteType_w CommonModification.quasiCompact_w

/-- **A blow-up of the strict transform extends to an admissible blow-up of the base**
(the second half of the construction of Stacks Project Tag 0F3X). Let `X` be qcqs, `U ⊆ X`
an open contained in the range of a quasi-compact morphism `p : V ⟶ X`, and `B` a
`U`-admissible blow-up of `X` whose strict transform of `p` is an open immersion into the
blown-up scheme `X'`. By Stacks Project Tag 080E
(`Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`) that strict transform is
the blow-up of `V` at the pulled-back centre `B.I.comap p`, so a further finite-type centre
`M` on it, whose support avoids the locus over `U`, has a blow-up `Bl_M` which is a blow-up
of an open subscheme of `X'`. Extending `M` across that open
(`IsAdmissible.exists_extend`) and composing the two admissible blow-ups
(`IsAdmissible.exists_comp`) exhibits `Bl_M` as an open subscheme of a single
`U`-admissible blow-up of `X`, lying over `V` as prescribed.
(Blueprint: part of `lemma:nagata-common-modification`.) -/
theorem IsAdmissible.exists_isOpenImmersion_blowup {X V : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (p : V ⟶ X) [QuasiCompact p]
    (hpU : (U : Set X) ⊆ Set.range p) (B : IsAdmissible X U)
    (hB : IsOpenImmersion (strictTransformMap p B.I.blowupMap B.preservedOpen))
    (M : (B.I.comap p).blowup.IdealSheafData) (hM : M.ofFiniteType)
    (hdisj : Disjoint (⇑((B.I.comap p).blowupMap ≫ p) ⁻¹' (U : Set X))
      (M.support : Set (B.I.comap p).blowup)) :
    ∃ (C : IsAdmissible X U) (m : M.blowup ⟶ C.I.blowup), IsOpenImmersion m ∧
      m ≫ C.I.blowupMap = M.blowupMap ≫ (B.I.comap p).blowupMap ≫ p := by
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  haveI := B.isProper_blowupMap
  haveI : QuasiCompact B.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap B.finiteType
  haveI : CompactSpace B.I.blowup := QuasiCompact.compactSpace_of_compactSpace B.I.blowupMap
  haveI : QuasiSeparatedSpace B.I.blowup := quasiSeparatedSpace_of_quasiSeparated B.I.blowupMap
  haveI : QuasiCompact (B.I.comap p).blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap (B.finiteType.comap p)
  haveI : CompactSpace (B.I.comap p).blowup :=
    QuasiCompact.compactSpace_of_compactSpace (B.I.comap p).blowupMap
  -- Tag 080E: the strict transform of `p` is the blow-up of the pulled-back centre, and it
  -- is an open subscheme of `X'` containing the whole locus over `U`.
  obtain ⟨q, hqOI, hq, hqrange⟩ : ∃ q : (B.I.comap p).blowup ⟶ B.I.blowup,
      IsOpenImmersion q ∧ q ≫ B.I.blowupMap = (B.I.comap p).blowupMap ≫ p ∧
      ∀ x' : B.I.blowup, B.I.blowupMap x' ∈ U → x' ∈ Set.range ⇑q := by
    haveI := hB
    obtain ⟨e, -, he⟩ := B.I.exists_blowup_comap_iso_strictTransform p
    refine ⟨e.hom ≫ strictTransformMap p B.I.blowupMap B.preservedOpen, inferInstance, he,
      fun x' hx' ↦ ?_⟩
    obtain ⟨t, ht⟩ := mem_range_strictTransformMap_of_mem_of_mem_range p B.I.blowupMap
      B.preservedOpen (B.le_preservedOpen hx') (hpU hx')
    have hsurj : Function.Surjective ⇑e.hom := by
      have h := (Scheme.homeoOfIso e).surjective
      rwa [Scheme.coe_homeoOfIso] at h
    obtain ⟨t', rfl⟩ := hsurj t
    exact ⟨t', by rw [Scheme.Hom.comp_apply]; exact ht⟩
  haveI := hqOI
  -- the strict transform as an open subscheme `T` of `X'`
  set T : B.I.blowup.Opens := q.opensRange with hTdef
  set φ : (B.I.comap p).blowup ≅ T.toScheme := q.isoOpensRange with hφdef
  have hφι : φ.hom ≫ T.ι = q := q.isoOpensRange_hom_ι
  have hφinv : ∀ t : T.toScheme, q (φ.inv t) = T.ι t := by
    intro t
    rw [← hφι, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply φ.inv φ.hom, φ.inv_hom_id]
    simp
  -- transport the centre `M` to the open `T`
  obtain ⟨N, hNft, hNsupp, f, hf⟩ : ∃ N : T.toScheme.IdealSheafData, N.ofFiniteType ∧
      (N.support : Set T.toScheme) = ⇑φ.inv ⁻¹' (M.support : Set (B.I.comap p).blowup) ∧
      ∃ f : N.blowup ≅ M.blowup, f.hom ≫ M.blowupMap = N.blowupMap ≫ φ.inv := by
    obtain ⟨f, hf⟩ := Scheme.IdealSheafData.exists_blowup_comap_iso M φ.symm
    exact ⟨M.comap φ.inv, hM.comap _, by simp, f, hf⟩
  -- the locus over `U` is contained in `T`, and `T` is quasi-compact
  have hUT : B.I.blowupMap ⁻¹ᵁ U ≤ T := fun x' hx' ↦ hqrange x' hx'
  have hTcpt : IsCompact ((T : B.I.blowup.Opens) : Set B.I.blowup) := isCompact_range q.continuous
  -- the support of the transported centre avoids the locus over `U`
  have hdisjN : Disjoint
      ((T.ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U) : T.toScheme.Opens) : Set T.toScheme)
      (N.support : Set T.toScheme) := by
    rw [Set.disjoint_left]
    intro t ht htN
    rw [hNsupp] at htN
    refine Set.disjoint_left.mp hdisj ?_ htN
    have hmem : B.I.blowupMap (q (φ.inv t)) ∈ U := by
      rw [hφinv]
      exact ht
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply]
    exact hmem
  -- extend the centre across `T` and compose the two admissible blow-ups
  obtain ⟨C', h, hh, hpb⟩ := IsAdmissible.exists_extend hTcpt hUT N hNft hdisjN
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isPullback hpb inferInstance
  obtain ⟨K, hKft, hKdisj, iso, hiso⟩ := IsAdmissible.exists_comp B C'
  refine ⟨⟨K, hKft, hKdisj⟩, f.inv ≫ h ≫ iso.hom, inferInstance, ?_⟩
  have hfinv : f.inv ≫ N.blowupMap = M.blowupMap ≫ φ.hom := by
    rw [← cancel_mono φ.inv, Category.assoc, Category.assoc, φ.hom_inv_id, Category.comp_id,
      ← hf, Iso.inv_hom_id_assoc]
  calc (f.inv ≫ h ≫ iso.hom) ≫ K.blowupMap
      = f.inv ≫ h ≫ C'.I.blowupMap ≫ B.I.blowupMap := by
        rw [Category.assoc, Category.assoc, hiso]
    _ = f.inv ≫ N.blowupMap ≫ T.ι ≫ B.I.blowupMap := by rw [← Category.assoc h, hh,
        Category.assoc]
    _ = M.blowupMap ≫ (φ.hom ≫ T.ι) ≫ B.I.blowupMap := by
        rw [← Category.assoc, hfinv]
        simp only [Category.assoc]
    _ = M.blowupMap ≫ (B.I.comap p).blowupMap ≫ p := by rw [hφι, hq]

/-- **Existence of a common modification** (Stacks Project Tag 0F3X): two separated
finite-type models `X₁`, `X₂` over a qcqs base `S` of a common quasi-compact open `U`
admit a common modification: `U`-admissible blow-ups `X'ᵢ ⟶ Xᵢ` which glue along a
common open copy of the blown-up `U`-locus to a separated finite-type scheme over `S`.

The construction is the one of the blueprint: form the scheme-theoretic image
`X₁₂ ⊆ X₁ ×_S X₂` of `U`, eliminate the indeterminacy of both projections
(`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`), dominate the two center
ideals by their product (`Scheme.IdealSheafData.exists_blowup_mul_iso`) and extend the
resulting common blow-up of `X₁₂` across the open strict transforms.
(Blueprint: `lemma:nagata-common-modification`; proof order item 32.) -/
theorem nonempty_commonModification [CompactSpace S] [QuasiSeparatedSpace S]
    (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (hj : j₁ ≫ s₁ = j₂ ≫ s₂)
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁]
    [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂] :
    Nonempty (CommonModification s₁ s₂ j₁ j₂) := by
  -- Step 0: finiteness of the ambient schemes.
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace s₁
  haveI : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace s₂
  haveI : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated s₁
  haveI : QuasiSeparatedSpace X₂ := quasiSeparatedSpace_of_quasiSeparated s₂
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j₁
  haveI : IsSeparated (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  haveI : LocallyOfFiniteType (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  haveI : QuasiCompact (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  haveI : IsSeparated (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  haveI : LocallyOfFiniteType (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  haveI : QuasiCompact (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  -- Step 1: the graph `γ = (j₁, j₂) : U ⟶ X₁ ×_S X₂`, its scheme-theoretic image `X₁₂`
  -- and the two projections `p₁`, `p₂` of the latter.
  obtain ⟨γ, hγdef⟩ : ∃ g : U ⟶ pullback s₁ s₂, g = pullback.lift j₁ j₂ hj := ⟨_, rfl⟩
  have hγ₁ : γ ≫ pullback.fst s₁ s₂ = j₁ := by rw [hγdef]; exact pullback.lift_fst _ _ _
  have hγ₂ : γ ≫ pullback.snd s₁ s₂ = j₂ := by rw [hγdef]; exact pullback.lift_snd _ _ _
  haveI : QuasiCompact γ := quasiCompact_of_partialSection s₁ s₂ j₁ γ hγ₁
  obtain ⟨p₁, hp₁def⟩ : ∃ f : γ.image ⟶ X₁, f = γ.imageι ≫ pullback.fst s₁ s₂ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ f : γ.image ⟶ X₂, f = γ.imageι ≫ pullback.snd s₁ s₂ := ⟨_, rfl⟩
  haveI : IsSeparated p₁ := by rw [hp₁def]; infer_instance
  haveI : LocallyOfFiniteType p₁ := by rw [hp₁def]; infer_instance
  haveI : QuasiCompact p₁ := by rw [hp₁def]; infer_instance
  haveI : IsSeparated p₂ := by rw [hp₂def]; infer_instance
  haveI : LocallyOfFiniteType p₂ := by rw [hp₂def]; infer_instance
  haveI : QuasiCompact p₂ := by rw [hp₂def]; infer_instance
  have hcomm : p₁ ≫ s₁ = p₂ ≫ s₂ := by
    rw [hp₁def, hp₂def, Category.assoc, Category.assoc, pullback.condition]
  have htoIm₁ : γ.toImage ≫ p₁ = j₁ := by
    rw [hp₁def, ← Category.assoc, Scheme.Hom.toImage_imageι, hγ₁]
  have htoIm₂ : γ.toImage ≫ p₂ = j₂ := by
    rw [hp₂def, ← Category.assoc, Scheme.Hom.toImage_imageι, hγ₂]
  -- Step 2: both projections are isomorphisms over the copies of `U`, whose inverse images
  -- in `X₁₂` are both the range of `γ.toImage`.
  haveI hiso₁ : IsIso (p₁ ∣_ j₁.opensRange) := by
    rw [hp₁def]; exact isIso_restrict_imageι_comp_fst s₁ s₂ j₁ γ hγ₁
  haveI hOItoIm : IsOpenImmersion γ.toImage :=
    isOpenImmersion_of_comp_of_isIso_restrict γ.toImage p₁ j₁ htoIm₁ hiso₁
  have hr₁ : Set.range ⇑γ.toImage = ⇑p₁ ⁻¹' Set.range ⇑j₁ :=
    range_eq_preimage_of_comp_of_isIso_restrict γ.toImage p₁ j₁ htoIm₁ hiso₁
  have hr₂ : ⇑p₂ ⁻¹' Set.range ⇑j₂ = Set.range ⇑γ.toImage := by
    rw [hp₂def]; exact preimage_range_snd_eq_range_toImage s₁ s₂ γ j₂ hγ₂
  haveI hiso₂ : IsIso (p₂ ∣_ j₂.opensRange) := by
    have hinv : j₂.isoOpensRange.inv ≫ j₂ = j₂.opensRange.ι := by
      rw [Iso.inv_comp_eq]
      exact (Scheme.Hom.isoOpensRange_hom_ι j₂).symm
    have hsurj : Function.Surjective ⇑j₂.isoOpensRange.inv := by
      have h := (Scheme.homeoOfIso j₂.isoOpensRange.symm).surjective
      rwa [Scheme.coe_homeoOfIso, Iso.symm_hom] at h
    refine isIso_morphismRestrict_of_range_eq p₂ j₂.opensRange
      (j₂.isoOpensRange.inv ≫ γ.toImage) ?_ ?_
    · rw [Category.assoc, htoIm₂, hinv]
    · rw [show ((p₂ ⁻¹ᵁ j₂.opensRange : γ.image.Opens) : Set γ.image) =
        ⇑p₂ ⁻¹' Set.range ⇑j₂ from rfl, hr₂, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  -- Step 3: elimination of indeterminacy for both projections (Tag 081S).
  have hU₁ : IsCompact ((j₁.opensRange : X₁.Opens) : Set X₁) := isCompact_range j₁.continuous
  have hU₂ : IsCompact ((j₂.opensRange : X₂.Opens) : Set X₂) := isCompact_range j₂.continuous
  obtain ⟨B₁, hB₁⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU₁ p₁ hiso₁
  obtain ⟨B₂, hB₂⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU₂ p₂ hiso₂
  have hK₁ft : (B₁.I.comap p₁).ofFiniteType := B₁.finiteType.comap p₁
  have hK₂ft : (B₂.I.comap p₂).ofFiniteType := B₂.finiteType.comap p₂
  have hK₁supp : ((B₁.I.comap p₁).support : Set γ.image) = ⇑p₁ ⁻¹' (B₁.I.support : Set X₁) := by
    simp
  have hK₂supp : ((B₂.I.comap p₂).support : Set γ.image) = ⇑p₂ ⁻¹' (B₂.I.support : Set X₂) := by
    simp
  -- the ranges of the two projections contain the copies of `U`
  have hpU₁ : ((j₁.opensRange : X₁.Opens) : Set X₁) ⊆ Set.range ⇑p₁ := by
    rintro - ⟨t, rfl⟩
    exact ⟨γ.toImage t, by rw [← Scheme.Hom.comp_apply, htoIm₁]⟩
  have hpU₂ : ((j₂.opensRange : X₂.Opens) : Set X₂) ⊆ Set.range ⇑p₂ := by
    rintro - ⟨t, rfl⟩
    exact ⟨γ.toImage t, by rw [← Scheme.Hom.comp_apply, htoIm₂]⟩
  -- Step 4: the common modification of `X₁₂` is the blow-up of the product of the two
  -- pulled-back centres; it dominates both strict transforms.
  obtain ⟨L, hLdef⟩ : ∃ J : γ.image.IdealSheafData, J = (B₁.I.comap p₁) * (B₂.I.comap p₂) :=
    ⟨_, rfl⟩
  have hLft : L.ofFiniteType := by rw [hLdef]; exact hK₁ft.mul hK₂ft
  have hLsupp : (L.support : Set γ.image) =
      ((B₁.I.comap p₁).support : Set γ.image) ∪ ((B₂.I.comap p₂).support : Set γ.image) := by
    rw [hLdef, Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
  obtain ⟨a₁, ha₁⟩ : ∃ e : L.blowup ≅ ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).blowup,
      e.hom ≫ ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).blowupMap ≫
        (B₁.I.comap p₁).blowupMap = L.blowupMap := by
    rw [hLdef]
    exact Scheme.IdealSheafData.exists_blowup_mul_iso _ _
  obtain ⟨a₂, ha₂⟩ : ∃ e : L.blowup ≅ ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).blowup,
      e.hom ≫ ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).blowupMap ≫
        (B₂.I.comap p₂).blowupMap = L.blowupMap := by
    rw [hLdef, mul_comm (B₁.I.comap p₁) (B₂.I.comap p₂)]
    exact Scheme.IdealSheafData.exists_blowup_mul_iso _ _
  -- the two auxiliary centres avoid the locus over `U`
  have hdisj₁ : Disjoint
      (⇑((B₁.I.comap p₁).blowupMap ≫ p₁) ⁻¹' ((j₁.opensRange : X₁.Opens) : Set X₁))
      (((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).support :
        Set (B₁.I.comap p₁).blowup) := by
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap, hK₂supp] at hzs
    refine Set.disjoint_left.mp B₂.disjoint_support ?_ hzs
    have hmem : (B₁.I.comap p₁).blowupMap z ∈ ⇑p₁ ⁻¹' Set.range ⇑j₁ := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      exact hz
    rw [← hr₁, ← hr₂] at hmem
    exact hmem
  have hdisj₂ : Disjoint
      (⇑((B₂.I.comap p₂).blowupMap ≫ p₂) ⁻¹' ((j₂.opensRange : X₂.Opens) : Set X₂))
      (((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).support :
        Set (B₂.I.comap p₂).blowup) := by
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap, hK₁supp] at hzs
    refine Set.disjoint_left.mp B₁.disjoint_support ?_ hzs
    have hmem : (B₂.I.comap p₂).blowupMap z ∈ ⇑p₂ ⁻¹' Set.range ⇑j₂ := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      exact hz
    rw [hr₂, hr₁] at hmem
    exact hmem
  -- Step 5: extend both auxiliary blow-ups to `U`-admissible blow-ups of `X₁` and `X₂`,
  -- inside which the common modification `L.blowup` sits as an open subscheme.
  obtain ⟨C₁, m₁, hm₁OI, hm₁⟩ := IsAdmissible.exists_isOpenImmersion_blowup p₁ hpU₁ B₁ hB₁
    ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap) (hK₂ft.comap _) hdisj₁
  obtain ⟨C₂, m₂, hm₂OI, hm₂⟩ := IsAdmissible.exists_isOpenImmersion_blowup p₂ hpU₂ B₂ hB₂
    ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap) (hK₁ft.comap _) hdisj₂
  haveI := hm₁OI
  haveI := hm₂OI
  obtain ⟨n₁, hn₁def⟩ : ∃ n : L.blowup ⟶ C₁.I.blowup, n = a₁.hom ≫ m₁ := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂def⟩ : ∃ n : L.blowup ⟶ C₂.I.blowup, n = a₂.hom ≫ m₂ := ⟨_, rfl⟩
  haveI : IsOpenImmersion n₁ := by rw [hn₁def]; infer_instance
  haveI : IsOpenImmersion n₂ := by rw [hn₂def]; infer_instance
  have hn₁ : n₁ ≫ C₁.I.blowupMap = L.blowupMap ≫ p₁ := by
    rw [hn₁def, Category.assoc, hm₁, ← ha₁]
    simp only [Category.assoc]
  have hn₂ : n₂ ≫ C₂.I.blowupMap = L.blowupMap ≫ p₂ := by
    rw [hn₂def, Category.assoc, hm₂, ← ha₂]
    simp only [Category.assoc]
  -- Step 6: the copy of `U` in the common modification.
  have hdisjU : Disjoint ((γ.toImage.opensRange : γ.image.Opens) : Set γ.image)
      (L.support : Set γ.image) := by
    have hcoe : ((γ.toImage.opensRange : γ.image.Opens) : Set γ.image) =
        Set.range ⇑γ.toImage := rfl
    rw [Set.disjoint_left, hLsupp, hcoe]
    rintro t ht (h | h)
    · rw [hK₁supp] at h
      rw [hr₁] at ht
      exact Set.disjoint_left.mp B₁.disjoint_support ht h
    · rw [hK₂supp] at h
      rw [← hr₂] at ht
      exact Set.disjoint_left.mp B₂.disjoint_support ht h
  haveI : IsIso (L.blowupMap ∣_ γ.toImage.opensRange) := L.isIso_blowupMap_restrict hdisjU
  obtain ⟨u, hu⟩ : ∃ u : U ⟶ L.blowup, u ≫ L.blowupMap = γ.toImage :=
    ⟨(γ.toImage.isoOpensRange.hom ≫ inv (L.blowupMap ∣_ γ.toImage.opensRange)) ≫
      (L.blowupMap ⁻¹ᵁ γ.toImage.opensRange).ι, by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
  have hu₁ : (u ≫ n₁) ≫ C₁.I.blowupMap = j₁ := by
    rw [Category.assoc, hn₁, ← Category.assoc, hu, htoIm₁]
  have hu₂ : (u ≫ n₂) ≫ C₂.I.blowupMap = j₂ := by
    rw [Category.assoc, hn₂, ← Category.assoc, hu, htoIm₂]
  -- Step 7: glue `C₁.I.blowup` and `C₂.I.blowup` along the common modification.
  haveI := C₁.isProper_blowupMap
  haveI := C₂.isProper_blowupMap
  haveI : QuasiCompact C₁.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap C₁.finiteType
  haveI : QuasiCompact C₂.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap C₂.finiteType
  have hw : n₁ ≫ C₁.I.blowupMap ≫ s₁ = n₂ ≫ C₂.I.blowupMap ≫ s₂ :=
    calc n₁ ≫ C₁.I.blowupMap ≫ s₁ = (n₁ ≫ C₁.I.blowupMap) ≫ s₁ := (Category.assoc _ _ _).symm
      _ = (L.blowupMap ≫ p₁) ≫ s₁ := by rw [hn₁]
      _ = L.blowupMap ≫ p₂ ≫ s₂ := by rw [Category.assoc, hcomm]
      _ = (n₂ ≫ C₂.I.blowupMap) ≫ s₂ := by rw [hn₂, Category.assoc]
      _ = n₂ ≫ C₂.I.blowupMap ≫ s₂ := Category.assoc _ _ _
  -- the overlap is a closed subscheme of the fibre product, so the gluing is separated
  have hδ : IsClosedImmersion (pullback.lift n₁ n₂ hw) := by
    obtain ⟨δ, hδdef⟩ : ∃ d : L.blowup ⟶ pullback (C₁.I.blowupMap ≫ s₁)
        (C₂.I.blowupMap ≫ s₂), d = pullback.lift n₁ n₂ hw := ⟨_, rfl⟩
    rw [← hδdef]
    have hδ₁ : δ ≫ pullback.fst (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) = n₁ := by
      rw [hδdef]; exact pullback.lift_fst _ _ _
    have hδ₂ : δ ≫ pullback.snd (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) = n₂ := by
      rw [hδdef]; exact pullback.lift_snd _ _ _
    -- `δ` is a preimmersion: it is a closed immersion into the open locus over `n₁`
    haveI : IsPreimmersion δ := by
      rw [← partialSection_openι (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) n₁ δ hδ₁]
      infer_instance
    -- `δ` has closed range: it is universally closed, being universally closed over the
    -- separated comparison morphism to `X₁ ×_S X₂`
    haveI : IsProper L.blowupMap := L.isProper_blowupMap fun V ↦ hLft V le_top
    obtain ⟨θ, hθdef⟩ : ∃ t : pullback (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) ⟶
        pullback s₁ s₂, t = pullback.map (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) s₁ s₂
          C₁.I.blowupMap C₂.I.blowupMap (𝟙 S) (by simp) (by simp) := ⟨_, rfl⟩
    haveI : IsSeparated θ := by
      rw [hθdef]
      exact MorphismProperty.pullbackMap (P := @IsSeparated) inferInstance inferInstance rfl rfl
    have hθ : δ ≫ θ = L.blowupMap ≫ γ.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hθdef, pullback.lift_fst, ← Category.assoc, hδ₁, hn₁,
          Category.assoc, hp₁def]
      · rw [Category.assoc, hθdef, pullback.lift_snd, ← Category.assoc, hδ₂, hn₂,
          Category.assoc, hp₂def]
    haveI : UniversallyClosed (δ ≫ θ) := by rw [hθ]; infer_instance
    haveI : UniversallyClosed δ := UniversallyClosed.of_comp_of_isSeparated δ θ
    refine IsClosedImmersion.of_isPreimmersion δ ?_
    rw [← Set.image_univ]
    exact δ.isClosedMap _ isClosed_univ
  exact ⟨{ B₁ := C₁, B₂ := C₂, W := pushout n₁ n₂
           w := pushout.desc (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) hw
           k₁ := pushout.inl n₁ n₂, k₂ := pushout.inr n₁ n₂
           isOpenImmersion_k₁ := inferInstance, isOpenImmersion_k₂ := inferInstance
           k₁_w := pushout.inl_desc _ _ _, k₂_w := pushout.inr_desc _ _ _
           u₁ := u ≫ n₁, u₂ := u ≫ n₂
           u₁_blowupMap := hu₁, u₂_blowupMap := hu₂
           u_glue := by rw [Category.assoc, Category.assoc, pushout.condition]
           cover := range_pushout_inl_union_range_pushout_inr n₁ n₂
           isSeparated_w := IsSeparated.pushout_desc n₁ n₂ hw hδ
           locallyOfFiniteType_w := IsZariskiLocalAtSource.pushout_desc n₁ n₂ hw
             inferInstance inferInstance
           quasiCompact_w := QuasiCompact.pushout_desc n₁ n₂ hw }⟩

end CommonModification

section GraphExtension

variable {S U : Scheme.{u}}

/-- The data of a **graph extension** of a compactification `c` of a quasi-compact open
`V ⊆ U` (Stacks Project Tag 0F3Z): a `V`-admissible blow-up `B : Y^gr ⟶ c.Z` of the
compactification, an open subscheme `V^gr ⊆ Y^gr` and a proper morphism
`ψ : V^gr ⟶ U` over `S` extending the inclusion of `V`, such that `V` embeds in `V^gr`
as the whole inverse image of `V` and `ψ` is an isomorphism over `V`.
(Blueprint: `def:nagata-graph-extension`.) -/
structure Compactification.ProperExtension (u : U ⟶ S) (V : U.Opens)
    (c : Compactification (V.ι ≫ u)) where
  /-- The `V`-admissible blow-up of the compactification. -/
  B : IsAdmissible c.Z c.i.opensRange
  /-- The open subscheme `V^gr` of the blown-up compactification carrying the
  extension. -/
  Vgr : B.I.blowup.Opens
  /-- The proper extension `V^gr ⟶ U` of the inclusion of `V`. -/
  ψ : Vgr.toScheme ⟶ U
  /-- The open embedding of `V` into `V^gr`. -/
  v : V.toScheme ⟶ Vgr.toScheme
  /-- The extension is proper. -/
  isProper_ψ : IsProper ψ
  /-- The copy of `V` is an open subscheme of `V^gr`. -/
  isOpenImmersion_v : IsOpenImmersion v
  /-- The embedded copy of `V` lifts the open immersion of the compactification. -/
  v_blowupMap : v ≫ Vgr.ι ≫ B.I.blowupMap = c.i
  /-- The extension really extends the inclusion of `V`. -/
  v_ψ : v ≫ ψ = V.ι
  /-- The inverse image of `V` is exactly the embedded copy of `V`. -/
  range_v : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v
  /-- The extension is an isomorphism over `V`. -/
  isIso_ψ_restrict : IsIso (ψ ∣_ V)
  /-- The extension lies over `S`. -/
  ψ_u : ψ ≫ u = Vgr.ι ≫ B.I.blowupMap ≫ c.g

attribute [instance] Compactification.ProperExtension.isProper_ψ
  Compactification.ProperExtension.isOpenImmersion_v

/-- **Graph extension** (Stacks Project Tag 0F3Z): a compactification of a
quasi-compact open `V ⊆ U` extends, after a `V`-admissible blow-up of the
compactification, to a proper morphism `V^gr ⟶ U` restricting to the identity on `V`.
(Blueprint: `lemma:nagata-graph-extension`; proof order item 33.) -/
theorem Compactification.nonempty_properExtension
    [CompactSpace S] [QuasiSeparatedSpace S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (V : U.Opens) (hV : IsCompact (V : Set U)) (c : Compactification (V.ι ≫ u)) :
    Nonempty (Compactification.ProperExtension u V c) := by
  -- The graph construction of the blueprint: `V^gr` is the open strict transform of
  -- the scheme-theoretic image of the graph `V ⟶ c.Z ×_S U`, supplied by the
  -- partial-section lemma (`partialSectionRestrictIso`), the image transport
  -- lemma (`Scheme.Hom.ker_lift_admissibleBlowup`) and elimination of indeterminacy
  -- (`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`); `ψ` is the second
  -- projection, proper because `c.Z ×_S U ⟶ U` is proper
  -- (`isProper_imageι_comp_fst`).
  -- Step 0: finiteness of the ambient schemes and quasi-compactness of the inclusions.
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated u
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : QuasiSeparatedSpace c.Z := quasiSeparatedSpace_of_quasiSeparated c.g
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  -- Step 1: the graph `γ = (c.i, V.ι) : V ⟶ c.Z ×_S U` of the compactification, a
  -- partial section of the first projection over the open immersion `c.i`.
  obtain ⟨γ, hγfst, hγsnd⟩ : ∃ γ : V.toScheme ⟶ pullback c.g u,
      γ ≫ pullback.fst c.g u = c.i ∧ γ ≫ pullback.snd c.g u = V.ι :=
    ⟨pullback.lift c.i V.ι c.comm.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hqcγ : QuasiCompact γ := quasiCompact_of_partialSection c.g u c.i γ hγfst
  -- the two projections of the scheme-theoretic image of the graph
  let p : γ.image ⟶ c.Z := γ.imageι ≫ pullback.fst c.g u
  let ψ₀ : γ.image ⟶ U := γ.imageι ≫ pullback.snd c.g u
  have hψ₀def : ψ₀ = γ.imageι ≫ pullback.snd c.g u := rfl
  have : IsSeparated (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : LocallyOfFiniteType (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : QuasiCompact (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : IsSeparated p := inferInstanceAs (IsSeparated (γ.imageι ≫ pullback.fst c.g u))
  have : LocallyOfFiniteType p :=
    inferInstanceAs (LocallyOfFiniteType (γ.imageι ≫ pullback.fst c.g u))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (γ.imageι ≫ pullback.fst c.g u))
  -- Step 2: `p` is an isomorphism over the compact open `V₀ = c.i(V)`
  -- (`isIso_restrict_imageι_comp_fst`), so its indeterminacy can be eliminated.
  have hV₀ : IsCompact ((c.i.opensRange : c.Z.Opens) : Set c.Z) :=
    isCompact_range c.i.continuous
  have hpV₀ : IsIso (p ∣_ c.i.opensRange) := isIso_restrict_imageι_comp_fst c.g u c.i γ hγfst
  obtain ⟨B, hB⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hV₀ p hpV₀
  let π : B.I.blowup ⟶ c.Z := B.I.blowupMap
  let W : c.Z.Opens := B.preservedOpen
  haveI hOIst : IsOpenImmersion (strictTransformMap p π W) := hB
  -- `V^gr` is the open strict transform, and `ψ` the projection to `U` through the
  -- scheme-theoretic image of the graph.
  let Vgr : B.I.blowup.Opens := (strictTransformMap p π W).opensRange
  let e : strictTransform p π W ≅ Vgr.toScheme := (strictTransformMap p π W).isoOpensRange
  have he : e.hom ≫ Vgr.ι = strictTransformMap p π W :=
    (strictTransformMap p π W).isoOpensRange_hom_ι
  have hVgrι : Vgr.ι = e.inv ≫ strictTransformMap p π W := by
    rw [← he, Iso.inv_hom_id_assoc]
  let ψ : Vgr.toScheme ⟶ U := e.inv ≫ strictTransformToSource p π W ≫ ψ₀
  have hψdef : ψ = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ := rfl
  -- Step 3: the canonical lift `ℓ` of `c.i` along the blow-up, an open immersion with
  -- range the full preimage of `c.i(V)`.
  haveI hπV₀ : IsIso (π ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
  obtain ⟨ℓ, hℓπ⟩ : ∃ ℓ : V.toScheme ⟶ B.I.blowup, ℓ ≫ π = c.i :=
    ⟨(c.i.isoOpensRange.hom ≫ inv (π ∣_ c.i.opensRange)) ≫ (π ⁻¹ᵁ c.i.opensRange).ι, by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
  have hOIℓ : IsOpenImmersion ℓ :=
    isOpenImmersion_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  have hrangeℓ : Set.range ℓ = ⇑π ⁻¹' Set.range c.i :=
    range_eq_preimage_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  -- the canonical morphism to the image projects back to `c.i` and `V.ι`
  have htoImp : γ.toImage ≫ p = c.i := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.fst c.g u)
    rw [hγfst] at h
    exact h
  have hψ₀V : γ.toImage ≫ ψ₀ = V.ι := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.snd c.g u)
    rw [hγsnd] at h
    exact h
  -- Step 4: the embedding `v` of `V` into `V^gr`, through the open strict transform.
  obtain ⟨v, hvι, hvst⟩ : ∃ v : V.toScheme ⟶ Vgr.toScheme,
      v ≫ Vgr.ι = ℓ ∧ v ≫ e.inv ≫ strictTransformToSource p π W = γ.toImage := by
    have hcompk : γ.toImage ≫ p = ℓ ≫ π := by
      rw [htoImp, hℓπ]
    have hkfst : pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π = γ.toImage :=
      pullback.lift_fst _ _ _
    have hksnd : pullback.lift γ.toImage ℓ hcompk ≫ pullback.snd p π = ℓ :=
      pullback.lift_snd _ _ _
    have hkrange : Set.range (pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π ≫ p) ⊆
        (W : Set c.Z) := by
      rw [← Category.assoc, hkfst, htoImp]
      rintro - ⟨t, rfl⟩
      exact B.le_preservedOpen ⟨t, rfl⟩
    refine ⟨(strictTransformOpenLift p π W (pullback.lift γ.toImage ℓ hcompk) hkrange ≫
        strictTransformFactor p π W) ≫ e.hom, ?_, ?_⟩
    · rw [Category.assoc, he, Category.assoc, strictTransformFactor_strictTransformMap,
        strictTransformOpenLift_ι_assoc, hksnd]
    · rw [Category.assoc, Iso.hom_inv_id_assoc]
      simp only [strictTransformToSource]
      rw [Category.assoc, strictTransformFactor_ι_assoc, strictTransformOpenLift_ι_assoc,
        hkfst]
  -- Step 5: the extension `ψ` is proper: it is a closed immersion into the base change
  -- of the (proper) blow-up followed by the proper projection `SIm(γ) ⟶ U`.
  have hψ₀proper : IsProper ψ₀ := by
    have h1 : IsProper (pullback.snd c.g u) := MorphismProperty.pullback_snd _ _ c.isProper
    exact inferInstanceAs (IsProper (γ.imageι ≫ pullback.snd c.g u))
  have hψproper : IsProper ψ := by
    have h2 : IsProper (pullback.fst p π) :=
      MorphismProperty.pullback_fst _ _ B.isProper_blowupMap
    rw [hψdef]
    simp only [strictTransformToSource]
    infer_instance
  -- Step 6: `v` is an open immersion, since `ℓ` is one.
  have hOIv : IsOpenImmersion v := by
    have : IsOpenImmersion (v ≫ Vgr.ι) := by
      rw [hvι]
      exact hOIℓ
    exact IsOpenImmersion.of_comp v Vgr.ι
  -- Step 7: the compatibilities of `v` and `ψ`.
  have hvblow : v ≫ Vgr.ι ≫ π = c.i := by
    rw [← Category.assoc, hvι, hℓπ]
  have hvψ : v ≫ ψ = V.ι := by
    have h1 : v ≫ ψ = (v ≫ e.inv ≫ strictTransformToSource p π W) ≫ ψ₀ := by
      rw [hψdef]
      simp only [Category.assoc]
    rw [h1, hvst, hψ₀V]
  have hpsq : ψ₀ ≫ u = p ≫ c.g := by
    have h : (γ.imageι ≫ pullback.snd c.g u) ≫ u =
        (γ.imageι ≫ pullback.fst c.g u) ≫ c.g := by
      simp only [Category.assoc, ← pullback.condition]
    exact h
  have hψu : ψ ≫ u = Vgr.ι ≫ π ≫ c.g := by
    calc ψ ≫ u = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ ≫ u := by
          rw [hψdef]
          simp only [Category.assoc]
      _ = e.inv ≫ strictTransformToSource p π W ≫ p ≫ c.g := by rw [hpsq]
      _ = e.inv ≫ (strictTransformToSource p π W ≫ p) ≫ c.g := by
          simp only [Category.assoc]
      _ = e.inv ≫ (strictTransformMap p π W ≫ π) ≫ c.g := by
          rw [strictTransform_condition]
      _ = (e.inv ≫ strictTransformMap p π W) ≫ π ≫ c.g := by
          simp only [Category.assoc]
      _ = Vgr.ι ≫ π ≫ c.g := by rw [← hVgrι]
  -- Step 8: the inverse image of `V` under `ψ` is exactly the embedded copy of `V`.
  have hrangev : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v := by
    apply subset_antisymm
    · -- a point of `V^gr` over `V` lies on the embedded copy of `V`: its image in
      -- `SIm(γ)` is a limit point of the graph lying over `V`, hence on the graph
      -- (`closure_range_inter_preimage_range_snd_subset`), and the lift `ℓ` then
      -- recovers it as the image of a point of `V`.
      intro t ht
      have htV : ψ t ∈ Set.range V.ι := by
        rw [Scheme.Opens.range_ι]
        exact ht
      have hψt : ψ t = ψ₀ (strictTransformToSource p π W (e.inv t)) := by
        rw [hψdef]
        simp only [Scheme.Hom.comp_apply]
      have hcl : γ.imageι (strictTransformToSource p π W (e.inv t)) ∈
          closure (Set.range γ) := by
        rw [← Scheme.Hom.support_ker γ, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      have hsndz : pullback.snd c.g u
          (γ.imageι (strictTransformToSource p π W (e.inv t))) ∈ Set.range V.ι := by
        rw [← Scheme.Hom.comp_apply, ← hψ₀def, ← hψt]
        exact htV
      obtain ⟨v₀, hv₀⟩ := closure_range_inter_preimage_range_snd_subset c.g u γ V.ι hγsnd
        ⟨hcl, hsndz⟩
      have htoim : γ.imageι (γ.toImage v₀) = γ v₀ := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
      have hz₀ : strictTransformToSource p π W (e.inv t) = γ.toImage v₀ :=
        γ.imageι.isClosedEmbedding.injective (by rw [htoim, hv₀])
      have hπVgr : π (Vgr.ι t) = c.i v₀ := by
        calc π (Vgr.ι t) = (Vgr.ι ≫ π) t := (Scheme.Hom.comp_apply _ _ _).symm
          _ = ((e.inv ≫ strictTransformMap p π W) ≫ π) t := by rw [hVgrι]
          _ = (e.inv ≫ strictTransformToSource p π W ≫ p) t := by
              rw [Category.assoc, ← strictTransform_condition]
          _ = p (strictTransformToSource p π W (e.inv t)) := by
              simp only [Scheme.Hom.comp_apply]
          _ = p (γ.toImage v₀) := by rw [hz₀]
          _ = (γ.toImage ≫ p) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
          _ = c.i v₀ := by rw [htoImp]
      have hbmem : Vgr.ι t ∈ Set.range ℓ := by
        rw [hrangeℓ]
        exact ⟨v₀, hπVgr.symm⟩
      obtain ⟨v₁, hv₁⟩ := hbmem
      have hv₁₀ : v₁ = v₀ := by
        apply c.i.isOpenEmbedding.injective
        calc c.i v₁ = (ℓ ≫ π) v₁ := by rw [hℓπ]
          _ = π (ℓ v₁) := Scheme.Hom.comp_apply _ _ _
          _ = π (Vgr.ι t) := by rw [hv₁]
          _ = c.i v₀ := hπVgr
      refine ⟨v₀, Vgr.ι.isOpenEmbedding.injective ?_⟩
      calc Vgr.ι (v v₀) = (v ≫ Vgr.ι) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ℓ v₀ := by rw [hvι]
        _ = ℓ v₁ := by rw [hv₁₀]
        _ = Vgr.ι t := hv₁
    · -- conversely the embedded copy of `V` lies over `V`, since `v ≫ ψ = V.ι`
      rintro - ⟨v₀, rfl⟩
      have hmem : ψ (v v₀) ∈ (V : Set U) := by
        rw [← Scheme.Hom.comp_apply, hvψ, ← Scheme.Opens.range_ι]
        exact ⟨v₀, rfl⟩
      exact hmem
  -- Step 9: `ψ` restricts to an isomorphism over `V`.
  have hisoψ : IsIso (ψ ∣_ V) := isIso_morphismRestrict_of_range_eq ψ V v hvψ hrangev
  exact ⟨{ B := B, Vgr := Vgr, ψ := ψ, v := v, isProper_ψ := hψproper,
           isOpenImmersion_v := hOIv, v_blowupMap := hvblow, v_ψ := hvψ,
           range_v := hrangev, isIso_ψ_restrict := hisoψ, ψ_u := hψu }⟩

end GraphExtension

section IsomorphismNearClosure

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W): let
`X` be qcqs, `U ⊆ X` a quasi-compact open, `q : Z ⟶ X` proper and `T ⊆ U` a subset
closed in `U` such that `q` is an isomorphism over an open neighbourhood `N` of `T`.
Then there is a `U`-admissible blow-up `B` of `X` such that the strict transform of `q`
is an isomorphism over an open neighbourhood of the closure of `T` in the blown-up
scheme.

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
proper) range of the strict transform. No scheme-theoretic density argument is used.
(Blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection
of the two-open compactification theorem.) -/
theorem exists_admissibleBlowup_isIso_strictTransformMap_near_closure
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ (B : IsAdmissible X U) (N' : B.I.blowup.Opens),
      closure (B.I.blowupMap ⁻¹' T) ⊆ (N' : Set B.I.blowup) ∧
      IsIso (strictTransformMap q B.I.blowupMap B.preservedOpen ∣_ N') := by
  haveI : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  -- Step 0: `T` lies in the maximal isomorphism open `M` of `q`, and `M` lies in the
  -- image of `q`.
  set M : X.Opens := q.maximalIsomorphismOpen with hMdef
  have hqM : IsIso (q ∣_ M) := q.isIso_restrict_maximalIsomorphismOpen
  have hTM : T ⊆ (M : Set X) := hTN.trans fun _ hx ↦ q.le_maximalIsomorphismOpen hN hx
  have hMrange : (M : Set X) ⊆ Set.range q := by
    intro x hx
    haveI := hqM
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
  haveI : IsProper B₁.I.blowupMap := B₁.isProper_blowupMap
  haveI : QuasiCompact B₁.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap B₁.finiteType
  haveI : CompactSpace B₁.I.blowup :=
    QuasiCompact.compactSpace_of_compactSpace B₁.I.blowupMap
  haveI : QuasiSeparatedSpace B₁.I.blowup :=
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
  haveI : IsProper (B₁.I.comap q).blowupMap :=
    (B₁.I.comap q).isProper_blowupMap fun V ↦ hcqft V le_top
  obtain ⟨lam₁, hlam₁⟩ := B₁.I.exists_lift_blowup
    (t := (B₁.I.comap q).blowupMap ≫ q)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (B₁.I.comap q).isInvertible_comap_blowupMap)
  haveI : IsProper (lam₁ ≫ B₁.I.blowupMap) := by rw [hlam₁]; infer_instance
  haveI : IsProper lam₁ := IsProper.of_comp lam₁ B₁.I.blowupMap
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
    haveI := hπZV₂
    haveI := hqV₂
    rw [morphismRestrict_comp]
    infer_instance
  -- Step 5: elimination of indeterminacy on the blow-up, over the locus above `V₂`.
  obtain ⟨B', hB'⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap
    (B₁.I.blowupMap.isCompact_preimage hV₂c) lam₁ hlam₁iso
  obtain ⟨eC, -, heC⟩ := B'.I.exists_blowup_comap_iso_strictTransform lam₁
  set lamC : (B'.I.comap lam₁).blowup ⟶ B'.I.blowup :=
    eC.hom ≫ strictTransformMap lam₁ B'.I.blowupMap B'.I.support.compl with hlamCdef
  haveI : IsOpenImmersion lamC := by
    haveI := hB'
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
  haveI : IsProper K.blowupMap := K.isProper_blowupMap fun V ↦ hKft V le_top
  haveI : IsProper (K.comap q).blowupMap :=
    (K.comap q).isProper_blowupMap fun V ↦ hKcqft V le_top
  -- Step 8: the canonical lifts on the composite blow-up and their comparison.
  obtain ⟨eK, -, heK⟩ := K.exists_blowup_comap_iso_strictTransform q
  set st : K.strictTransform q ⟶ K.blowup :=
    strictTransformMap q K.blowupMap K.support.compl with hstdef
  set lamK : (K.comap q).blowup ⟶ K.blowup := eK.hom ≫ st with hlamKdef
  have hlamK : lamK ≫ K.blowupMap = (K.comap q).blowupMap ≫ q := heK
  haveI : IsProper (lamK ≫ K.blowupMap) := by rw [hlamK]; infer_instance
  haveI : IsProper lamK := IsProper.of_comp lamK K.blowupMap
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
  haveI := hCOI
  haveI := hC'OI
  haveI : IsOpenImmersion mu := by
    haveI : IsOpenImmersion (mu ≫ hC) := by
      rw [← hCsq]
      infer_instance
    exact IsOpenImmersion.of_comp mu hC
  obtain ⟨hD, hD', hDOI, hD'OI, hDsq, hDrange, hD'range⟩ :=
    Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens D lam₁ A hDA hlamD hmu
  haveI := hDOI
  haveI := hD'OI
  -- Step 9: the partial section of the strict transform over the copy of `A`.
  set m : (JA.comap (lam₁ ∣_ A)).blowup ⟶ (K.comap q).blowup := hD' ≫ be.inv with hmdef
  haveI : IsOpenImmersion m := by rw [hmdef]; infer_instance
  have hjeq : m ≫ lamK = mu ≫ hD ≫ al.inv := by
    rw [hmdef, Category.assoc, hcompat, ← Category.assoc, hDsq, Category.assoc]
  haveI : IsOpenImmersion (m ≫ lamK) := by rw [hjeq]; infer_instance
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
  haveI : IsOpenImmersion ((m ≫ eK.hom) ≫ st) := by rw [hmst]; infer_instance
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

end IsomorphismNearClosure

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
