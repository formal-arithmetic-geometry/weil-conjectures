/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.SchemeTheoreticImage

/-!

# Finite-type extension of ideals: the affine algebra layer

This file begins Phase A of the formalization plan
`blueprint/stacks_01PH_01PF_080L_0F3V_formalization_blueprint.md` for the Stacks
Project tags 01PF (finite-type extension of quasi-coherent submodules) and 01PH
(quasi-compact opens are complements of finite-type vanishing loci), which are the
remaining leaves of `WeilConjectures.Compactification.Flattening`.

We prove the affine finite-generation core of Tag 01PF (blueprint §1.2.B): if an ideal
`N` of a ring `R` has finitely generated localizations at each element of a finite set
`s`, then a single finitely generated subideal `N' ≤ N` realizes all those
localizations simultaneously. The proof clears the finitely many localization
denominators, replacing each generator `x/fᵏ` of a localized ideal by its numerator.

We also prove the compactness micro-lemma of blueprint §2.4: the complement of the
vanishing locus of a finitely generated ideal in the prime spectrum is quasi-compact,
being the finite union of the basic opens at the generators.

## Main results

- `Ideal.exists_fg_le_map_localization_eq`: the affine clearing-denominators lemma
  (blueprint §1.2.B, `Submodule.exists_fg_eq_localization_on_finset`);
- `Ideal.FG.isCompact_compl_zeroLocus`: quasi-compactness of the complement of the
  vanishing locus of a finitely generated ideal (blueprint §2.4);
- `Scheme.Opens.quasiCompact_ι`: the inclusion of a quasi-compact open of a
  quasi-separated scheme is a quasi-compact morphism (blueprint §2.2,
  retrocompactness);
- `Scheme.IdealSheafData.openExtension` and
  `Scheme.IdealSheafData.comap_openExtension`: the canonical quasi-coherent extension
  of an ideal sheaf from a retrocompact open, with its restriction identity
  (Stacks Project Tag 01PE, ideal form; blueprint §1.2.A), realized as the kernel of
  `Z_J ↪ W ↪ X` and computed by flat base change of scheme-theoretic images.

The remaining Phase A milestone is the finite-type refinement (Tag 01PF): produce a
finite-type ideal subsheaf of `openExtension W J` with the same restriction to `W`.
Per blueprint §1.2.B–C this combines `Ideal.exists_fg_le_map_localization_eq` on the
members of a finite affine cover with a binary gluing of ideal subsheaves and an
induction over the cover; the gluing interface for `IdealSheafData` does not exist yet
and is the concrete missing piece.

-/

@[expose] public section

universe u

section ClearingDenominators

variable {R : Type u} [CommRing R]

/-- One localization at a time: if the localization of `N` away from `f` is finitely
generated, there is a finite set of elements of `N` whose images generate it. The
generators of the localized ideal are multiplied by their denominators, which are
units in the localization. -/
lemma Ideal.exists_finset_span_image_eq_map_localization (N : Ideal R) (f : R)
    (H : (N.map (algebraMap R (Localization.Away f))).FG) :
    ∃ T : Finset R, (T : Set R) ⊆ (N : Set R) ∧
      Ideal.span (algebraMap R (Localization.Away f) '' T) =
        N.map (algebraMap R (Localization.Away f)) := by
  classical
  obtain ⟨G, hG⟩ := H
  have hmem : ∀ y ∈ G, y ∈ N.map (algebraMap R (Localization.Away f)) := by
    intro y hy
    rw [← hG]
    exact Ideal.subset_span hy
  choose nm hnm using fun (y : G) ↦
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)
      (Localization.Away f)).mp (hmem y y.2)
  refine ⟨G.attach.image (fun y ↦ ((nm y).1 : R)), ?_, le_antisymm ?_ ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact (nm y).1.2
  · rw [Ideal.span_le]
    rintro z ⟨x, hx, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact Ideal.mem_map_of_mem _ (nm y).1.2
  · rw [← hG, Ideal.span_le]
    intro y hy
    have h1 : y * algebraMap R (Localization.Away f) ((nm ⟨y, hy⟩).2 : R) =
        algebraMap R (Localization.Away f) ((nm ⟨y, hy⟩).1 : R) := hnm ⟨y, hy⟩
    obtain ⟨u, hu⟩ : IsUnit (algebraMap R (Localization.Away f) ((nm ⟨y, hy⟩).2 : R)) :=
      IsLocalization.map_units (Localization.Away f) (nm ⟨y, hy⟩).2
    have hy2 : y = algebraMap R (Localization.Away f) ((nm ⟨y, hy⟩).1 : R) * ↑u⁻¹ := by
      rw [← h1, ← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hy2]
    refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
    refine Set.mem_image_of_mem _ ?_
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩

/-- **The affine clearing-denominators lemma** (Stacks Project Tag 01PF, affine core;
blueprint §1.2.B): if the localizations of an ideal `N` away from each member of a
finite set `s` are finitely generated, then there is a single finitely generated
subideal `N' ≤ N` whose localization away from each `f ∈ s` agrees with that of
`N`. -/
theorem Ideal.exists_fg_le_map_localization_eq (N : Ideal R) (s : Finset R)
    (H : ∀ f ∈ s, (N.map (algebraMap R (Localization.Away f))).FG) :
    ∃ N' : Ideal R, N' ≤ N ∧ N'.FG ∧ ∀ f ∈ s,
      N'.map (algebraMap R (Localization.Away f)) =
        N.map (algebraMap R (Localization.Away f)) := by
  classical
  choose T hTsub hTspan using fun (f : s) ↦
    N.exists_finset_span_image_eq_map_localization f (H f f.2)
  refine ⟨Ideal.span (s.attach.biUnion T : Finset R), ?_, ⟨_, rfl⟩, ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    rw [Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨f, -, hf⟩ := hx
    exact hTsub f (Finset.mem_coe.mpr hf)
  · intro f hf
    refine le_antisymm (Ideal.map_mono ?_) ?_
    · rw [Ideal.span_le]
      intro x hx
      rw [Finset.mem_coe, Finset.mem_biUnion] at hx
      obtain ⟨g, -, hg⟩ := hx
      exact hTsub g (Finset.mem_coe.mpr hg)
    · rw [← hTspan ⟨f, hf⟩]
      refine Ideal.span_le.mpr ?_
      rintro z ⟨x, hx, rfl⟩
      refine Ideal.mem_map_of_mem _ (Ideal.subset_span ?_)
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨⟨f, hf⟩, Finset.mem_attach _ _, Finset.mem_coe.mp hx⟩

/-- **Quasi-compactness of the complement of a finitely generated vanishing locus**
(blueprint §2.4): the complement of `V(I)` in the prime spectrum of `R` is
quasi-compact for a finitely generated ideal `I`, being the finite union of the basic
opens at the generators. -/
theorem Ideal.FG.isCompact_compl_zeroLocus {I : Ideal R} (hI : I.FG) :
    IsCompact (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  have h1 : (PrimeSpectrum.zeroLocus ((Ideal.span (s : Set R) : Ideal R) : Set R))ᶜ =
      ⋃ f ∈ s, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    ext x
    simp [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  rw [h1]
  exact s.finite_toSet.isCompact_biUnion fun f _ ↦ PrimeSpectrum.isCompact_basicOpen f

end ClearingDenominators

section OpenExtension

open AlgebraicGeometry CategoryTheory Limits

variable {X : Scheme.{u}} (W : X.Opens)

/-- **Retrocompactness** (blueprint §2.2): the inclusion of a quasi-compact open of a
quasi-separated scheme is a quasi-compact morphism. -/
theorem Scheme.Opens.quasiCompact_ι [QuasiSeparatedSpace X]
    (hW : IsCompact (W : Set X)) : QuasiCompact W.ι := by
  constructor
  intro U hU hU'
  rw [W.ι.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι]
  exact QuasiSeparatedSpace.inter_isCompact U W hU hU' W.isOpen hW

variable (J : W.toScheme.IdealSheafData)

/-- **The canonical quasi-coherent extension of an ideal sheaf from an open**
(Stacks Project Tag 01PE, ideal form; blueprint §1.2.A): the kernel of the composite
of the closed subscheme of `J` with the open immersion `W.ι`. Its restriction back to
`W` is `J` (`Scheme.IdealSheafData.comap_openExtension`); it is quasi-coherent by
construction, but not finite type in general — the finite-type refinement is
Tag 01PF. -/
noncomputable def Scheme.IdealSheafData.openExtension : X.IdealSheafData :=
  (J.subschemeι ≫ W.ι).ker

/-- **The canonical extension restricts to the original ideal** (Stacks Project
Tag 01PE): pulling the extension back along the quasi-compact open immersion recovers
`J`. The proof identifies the restriction of the kernel with the kernel of the closed
immersion of `J` via flat base change of scheme-theoretic images
(`Nagata.schemeImageRestrictOpen`). -/
theorem Scheme.IdealSheafData.comap_openExtension [QuasiCompact W.ι] :
    (Scheme.IdealSheafData.openExtension W J).comap W.ι = J := by
  rw [Scheme.IdealSheafData.openExtension,
    ← AlgebraicGeometry.Nagata.schemeImageRestrictOpen (J.subschemeι ≫ W.ι) W.ι]
  have H : IsPullback (𝟙 J.subscheme) J.subschemeι (J.subschemeι ≫ W.ι) W.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp]⟩
  have hsnd : pullback.snd (J.subschemeι ≫ W.ι) W.ι =
      H.isoPullback.inv ≫ J.subschemeι :=
    ((Iso.inv_comp_eq _).mpr H.isoPullback_hom_snd.symm).symm
  rw [hsnd, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

end OpenExtension
