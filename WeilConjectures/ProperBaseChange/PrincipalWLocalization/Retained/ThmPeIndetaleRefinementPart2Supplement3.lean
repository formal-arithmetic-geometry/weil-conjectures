/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3

/-! # Retaining a closed subset in the principal w-localization

For a closed subset `T` of `Spec R`, the retained localization `R_[T]` is the colimit of the
localizations of the principal w-localization `R^w` at the idempotent selectors `e_E` of the
constructible supersets `E` of `T`.

## Implementation details

Selectors are constructed at the two-part partition into a constructible set and its
complement, omitting empty parts. Their localizations form a reverse-inclusion diagram.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

open Classical in
/-- The nonempty parts of the partition into `E` and its complement. -/
noncomputable def parts (E : Set (PrimeSpectrum R)) : Finset (Set (PrimeSpectrum R)) :=
  Finset.filter Set.Nonempty ({E, Eᶜ} : Finset (Set (PrimeSpectrum R)))

/-- For constructible `E`, the nonempty parts of `{E, Eᶜ}` are nonempty, constructible, partition
the spectrum, and lie in `D(1)`. -/
theorem parts_valid (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    (∀ F ∈ parts E, Set.Nonempty F) ∧
    (∀ F ∈ parts E, Topology.IsConstructible F) ∧
    (∀ p : PrimeSpectrum R, ∃! F : parts E, p ∈ F.val) ∧
    (∀ F : parts E, F.val ⊆ PrimeSpectrum.basicOpen (1 : R)) := by
  classical
  have mem_parts (F : Set (PrimeSpectrum R)) :
      F ∈ parts E ↔ (F = E ∨ F = Eᶜ) ∧ F.Nonempty := by
    simp [parts]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hF
    exact ((mem_parts F).mp hF).2
  · intro F hF
    rcases ((mem_parts F).mp hF).1 with rfl | rfl
    · exact hE
    · exact hE.compl
  · intro p
    by_cases hp : p ∈ E
    · refine ⟨⟨E, (mem_parts E).mpr ⟨Or.inl rfl, ⟨p, hp⟩⟩⟩, hp, ?_⟩
      intro F hF
      apply Subtype.ext
      rcases ((mem_parts F.val).mp F.property).1 with he | he
      · exact he
      · exact False.elim ((he ▸ hF) hp)
    · refine ⟨⟨Eᶜ, (mem_parts Eᶜ).mpr ⟨Or.inr rfl, ⟨p, hp⟩⟩⟩, hp, ?_⟩
      intro F hF
      apply Subtype.ext
      rcases ((mem_parts F.val).mp F.property).1 with he | he
      · exact False.elim (hp (he ▸ hF))
      · exact he
  · intro F p hp
    simp

/-- The partition index used to construct the selector, with constant denominator one. -/
noncomputable def selectorIndex (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    Index R where
  parts := parts E
  nonempty := (parts_valid E hE).1
  constructible := (parts_valid E hE).2.1
  partition := (parts_valid E hE).2.2.1
  denominator := fun _ ↦ 1
  nonvanishing := (parts_valid E hE).2.2.2

open Classical in
/-- The image in `R^w` of the stage element which is one on `E` and zero on its complement. -/
noncomputable def selector (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    algebra R :=
  (colimit.ι (diagram (A := R)) (selectorIndex E hE)).hom
    (fun F ↦ if F.val ⊆ E then 1 else 0)

/-- The selector is idempotent. -/
theorem selector_idempotent (E : Set (PrimeSpectrum R)) (hE : Topology.IsConstructible E) :
    IsIdempotentElem (selector E hE) := by
  classical
  apply IsIdempotentElem.map
  change (fun F : (selectorIndex E hE).parts ↦
    if F.val ⊆ E then (1 : Localization.Away ((selectorIndex E hE).denominator F))
    else 0) * _ = _
  funext F
  simp only [Pi.mul_apply]
  split_ifs <;> simp

/-- Constructible neighbourhoods of `T`, i.e. constructible supersets of `T`, ordered by
reverse inclusion. -/
abbrev Neighborhood (T : Set (PrimeSpectrum R)) :=
  OrderDual {E : Set (PrimeSpectrum R) // Topology.IsConstructible E ∧ T ⊆ E}

/-- The neighbourhood index is filtered. -/
theorem neighborhood_isFiltered (T : Set (PrimeSpectrum R)) : IsFiltered (Neighborhood T) := by
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := ?_ }
  · intro E F
    let G : Neighborhood T :=
      ⟨E.val ∩ F.val, E.property.1.inter F.property.1,
        fun p hp ↦ ⟨E.property.2 hp, F.property.2 hp⟩⟩
    exact ⟨G, homOfLE Set.inter_subset_left, homOfLE Set.inter_subset_right, trivial⟩
  · intro E F f g
    exact ⟨F, 𝟙 F, Subsingleton.elim _ _⟩
  · exact ⟨⟨Set.univ, Topology.IsConstructible.univ, Set.subset_univ T⟩⟩

attribute [instance] neighborhood_isFiltered

open Classical in
private theorem transition_selector (E : Set (PrimeSpectrum R))
    (hE : Topology.IsConstructible E) {j : Index R} (h : selectorIndex E hE ≤ j) :
    PrincipalWLocalization.transition h (fun P ↦ if P.val ⊆ E then 1 else 0) =
      (fun Q ↦ if Q.val ⊆ E then 1 else 0) := by
  classical
  funext Q
  have hsub : Q.val ⊆ (parent h Q).val := (Classical.choose_spec (h Q)).1
  have hiff : (parent h Q).val ⊆ E ↔ Q.val ⊆ E := by
    refine ⟨fun hP ↦ hsub.trans hP, ?_⟩
    intro hQ
    have hmem : (parent h Q).val ∈ parts E := (parent h Q).property
    have hcases : (parent h Q).val = E ∨ (parent h Q).val = Eᶜ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton]
        using (Finset.mem_filter.mp hmem).1
    rcases hcases with he | he
    · rw [he]
    · obtain ⟨p, hp⟩ := j.nonempty Q.val Q.property
      exact False.elim ((he ▸ hsub hp) (hQ hp))
  simp only [PrincipalWLocalization.transition, AlgHom.pi_apply, AlgHom.comp_apply,
    Pi.evalAlgHom_apply]
  simp only [hiff]
  split_ifs <;> simp

/-- For `F ⊆ E`, the selector of `E` is a unit after localizing at the selector of `F`. -/
theorem selector_isUnit {E F : Set (PrimeSpectrum R)}
    (hE : Topology.IsConstructible E) (hF : Topology.IsConstructible F) (hFE : F ⊆ E) :
    IsUnit (algebraMap (algebra R) (Localization.Away (selector F hF)) (selector E hE)) := by
  classical
  obtain ⟨j, f, g, _⟩ :=
    IsFilteredOrEmpty.cocone_objs (selectorIndex E hE) (selectorIndex F hF)
  have he : selector E hE = (colimit.ι (diagram (A := R)) j).hom
      (fun Q ↦ if Q.val ⊆ E then 1 else 0) := by
    rw [← transition_selector E hE f.le]
    exact (ConcreteCategory.congr_hom (colimit.w (diagram (A := R)) f) _).symm
  have hf : selector F hF = (colimit.ι (diagram (A := R)) j).hom
      (fun Q ↦ if Q.val ⊆ F then 1 else 0) := by
    rw [← transition_selector F hF g.le]
    exact (ConcreteCategory.congr_hom (colimit.w (diagram (A := R)) g) _).symm
  let c : Stage j →ₐ[R] PrincipalWLocalization.algebra R :=
    (colimit.ι (diagram (A := R)) j).hom
  have hmul : selector E hE * selector F hF = selector F hF := by
    rw [he, hf]
    change c _ * c _ = c _
    rw [← map_mul]
    apply congrArg c
    funext Q
    simp only [Pi.mul_apply]
    by_cases hQ : Q.val ⊆ F
    · simp [hQ, hQ.trans hFE]
    · simp [hQ]
  exact IsLocalization.Away.isUnit_of_dvd (selector F hF)
    ⟨selector F hF, hmul.symm⟩

/-- The transition is the unique `R^w`-algebra map between the selector localizations. -/
noncomputable def transition {T : Set (PrimeSpectrum R)} {E F : Neighborhood T} (h : E ≤ F) :
    Localization.Away (selector E.val E.property.1) →ₐ[algebra R]
      Localization.Away (selector F.val F.property.1) :=
  IsLocalization.Away.liftAlgHom (selector E.val E.property.1)
    (f := Algebra.ofId (algebra R) (Localization.Away (selector F.val F.property.1)))
    (selector_isUnit E.property.1 F.property.1 h)

/-- The transition along `E ≤ E` is the identity. -/
theorem transition_id {T : Set (PrimeSpectrum R)} (E : Neighborhood T) :
    transition (le_refl E) = AlgHom.id (algebra R)
      (Localization.Away (selector E.val E.property.1)) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (selector E.val E.property.1))
  ext

/-- Transitions compose. -/
theorem transition_comp {T : Set (PrimeSpectrum R)} {E F G : Neighborhood T}
    (hEF : E ≤ F) (hFG : F ≤ G) :
    transition (le_trans hEF hFG) = (transition hFG).comp (transition hEF) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (selector E.val E.property.1))
  ext

/-- The reverse-inclusion diagram of localizations at the constructible selectors. -/
noncomputable def localizationDiagram (T : Set (PrimeSpectrum R)) :
    Neighborhood T ⥤ CommAlgCat.{u} (algebra R) where
  obj E := CommAlgCat.of (algebra R) (Localization.Away (selector E.val E.property.1))
  map h := CommAlgCat.ofHom (transition h.le)
  map_id E := congrArg CommAlgCat.ofHom (transition_id E)
  map_comp h g := congrArg CommAlgCat.ofHom (transition_comp h.le g.le)

/-- The retained localization `R_[T]` is the colimit of `(R^w)[1/e_E]` over all constructible
supersets `E` of the closed set `T`, with reverse-inclusion transition maps. -/
noncomputable def algebra (T : Set (PrimeSpectrum R)) (_hT : IsClosed T) :
    CommAlgCat.{u} (PrincipalWLocalization.algebra R) :=
  colimit (localizationDiagram T)

end PrincipalWLocalization.Retained
