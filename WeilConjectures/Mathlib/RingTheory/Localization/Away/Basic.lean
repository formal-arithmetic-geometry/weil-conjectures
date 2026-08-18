/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite generation of ideals along localizations away from an element

Clearing denominators: an ideal whose localizations away from the elements of a finite
set are finitely generated already has a finitely generated subideal realizing all of
those localizations (`Ideal.exists_fg_le_map_localization_eq`); and finite generation
and equality of extended ideals transfer between the different models of a
localization away from an element (`Ideal.FG.map_localizationAway`,
`Ideal.map_eq_map_of_localizationAway`).

This is the affine core of Stacks Project Tag 01PF.
-/

@[expose] public section

universe u

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

/-- **Transfer of finite generation to the abstract localization**: if the extension of `N`
to some localization of `R` away from `f` is finitely generated, so is its extension to
`Localization.Away f`. This bridges the scheme-theoretic sections rings (which are
localizations via `IsAffineOpen.isLocalization_basicOpen`) and the abstract localizations
used by the clearing-denominators lemma. -/
lemma Ideal.FG.map_localizationAway {S : Type u} [CommRing S] [Algebra R S] {f : R}
    [IsLocalization.Away f S] {N : Ideal R} (H : (N.map (algebraMap R S)).FG) :
    (N.map (algebraMap R (Localization.Away f))).FG := by
  let e : S ≃ₐ[R] Localization.Away f :=
    IsLocalization.algEquiv (Submonoid.powers f) S (Localization.Away f)
  have h1 : N.map (algebraMap R (Localization.Away f)) =
      (N.map (algebraMap R S)).map (e.toAlgHom : S →+* Localization.Away f) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  rw [h1]
  exact H.map _

/-- **Transfer of an equality of localized ideals along an `f`-inverting homomorphism**: if
two ideals of `R` have the same extension to `Localization.Away f`, they have the same
extension along every ring homomorphism inverting `f`. The homomorphism factors through the
localization by `IsLocalization.Away.lift`. -/
lemma Ideal.map_eq_map_of_localizationAway {T : Type u} [CommRing T] {χ : R →+* T} {f : R}
    (hf : IsUnit (χ f)) {N N' : Ideal R}
    (H : N.map (algebraMap R (Localization.Away f)) =
      N'.map (algebraMap R (Localization.Away f))) :
    N.map χ = N'.map χ := by
  have hχ : (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
      (algebraMap R (Localization.Away f)) = χ := IsLocalization.Away.lift_comp f hf
  rw [← hχ, ← Ideal.map_map, ← Ideal.map_map, H]

