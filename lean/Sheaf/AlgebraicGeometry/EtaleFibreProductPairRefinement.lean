module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Étale fibre products and Cartesian closed pairs

Source: Stacks Project, Tag 024T, proposition-properties-sections (3), and Tags
02GO, 01QR, 02GP, 02GN (blueprint: lem-trf-etale-fibre-product-pair-refinement).

The two projection identities characterize each graph section uniquely. The Cartesian
squares express the scheme-theoretic identifications, including their maps from `X`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem section_clopen {F X : Scheme.{u}} (q : F ⟶ X) (t : X ⟶ F)
    [Etale q] [IsSeparated q] (ht : t ≫ q = 𝟙 X) :
    IsOpenImmersion t ∧ IsClosedImmersion t := by
  have : IsSplitMono t := IsSplitMono.mk' ⟨q, ht⟩
  have : Etale (t ≫ q) := by rw [ht]; infer_instance
  have : Etale t := Etale.of_comp t q
  have : IsClosedImmersion (t ≫ q) := by rw [ht]; infer_instance
  exact ⟨IsOpenImmersion.of_flat_of_mono t, IsClosedImmersion.of_comp t q⟩

private theorem complement_closed {F X P : Scheme.{u}}
    (j : F ⟶ P) (t : X ⟶ F) [IsClosedImmersion j] [IsOpenImmersion t] :
    IsClosed (j '' (Set.range t)ᶜ) :=
  j.isClosedEmbedding.isClosedMap _ t.isOpenEmbedding.isOpen_range.isClosed_compl

private theorem section_avoids_complement {F X P : Scheme.{u}}
    (j : F ⟶ P) (t : X ⟶ F) [IsClosedImmersion j] (x : X) :
    (t ≫ j) x ∉ j '' (Set.range t)ᶜ := by
  rintro ⟨z, hz, he⟩
  apply hz
  exact ⟨x, (j.isClosedEmbedding.injective he).symm⟩

private theorem section_square {F X P M : Scheme.{u}}
    (j : F ⟶ P) (q : F ⟶ X) (p : P ⟶ M) (i : X ⟶ M)
    (sq : IsPullback j q p i) (t : X ⟶ F) [IsOpenImmersion t]
    (ht : t ≫ q = 𝟙 X) (U : P.Opens) (sU : X ⟶ U.toScheme)
    (hs : t ≫ j = sU ≫ U.ι)
    (hU : ∀ z : F, j z ∈ U ↔ z ∈ Set.range t) :
    IsPullback sU (𝟙 X) (U.ι ≫ p) i := by
  have hsq : IsPullback sU t U.ι j := by
    apply IsOpenImmersion.isPullback _ _ _ _ hs
    ext z
    simpa using hU z
  simpa only [ht] using hsq.paste_vert sq

private theorem residue_iso_of_surjective_stalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  change Function.Surjective (IsLocalRing.ResidueField.map (f.stalkMap x).hom)
  intro a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, hc⟩ := f.stalkMap_surjective x b
  refine ⟨IsLocalRing.residue _ c, ?_⟩
  simp only [IsLocalRing.ResidueField.map_residue, hc]

/-- Delete the closed complement of the graph section to obtain a Cartesian closed pair.
Source: Stacks Project, Tag 024T (3), with Tags 02GO, 01QR, 02GP, 02GN
(blueprint: lem-trf-etale-fibre-product-pair-refinement).

Proof: (1) The fibre-product universal property (def-pc-fibre-product) identifies
`F₁ = P ×_{M₁} X` with `X ×_S M₂`. The graph `(1, i₂)` is its section `t₁`;
its composite to `P` is `s = (i₁, i₂)`.
(2) Étale base change (lem-weil-pbc-etale-scheme-base-change) makes `p₁` and
`F₁ → X` étale; closed-immersion base change
(lem-weil-pbc-closed-immersion-base-change) makes `F₁ → P` closed.
An affine-source map is separated (lem-weil-pbc-affine-source-morphism-separated),
and pulling back its closed diagonal proves `F₁ → X` separated.
(3) The section is an open and closed immersion
(lem-weil-pbc-etale-section-clopen-immersion). Its complement is closed in `F₁`,
so its image under the closed immersion `F₁ → P` is closed in `P` and misses `s(X)`.
(4) Delete that image. Pulling back this open to `F₁` gives exactly the open
subscheme `t₁(X)`, isomorphic to `X`; hence the asserted square is Cartesian
with the full scheme structure, including nilpotents (def-weil-open-immersion).
(5) The restricted first projection is étale, as an open immersion followed by
an étale map (lem-weil-pbc-etale-composition-cancellation).
(6) When `e₁` is also étale, interchange the indices and repeat (1)--(4).
Delete both closed complements, or intersect the two opens. Since both contain
all of `s(X)`, both Cartesian identifications persist, and both projections are étale.
(7) The closed immersion `F₁ → P` induces a surjective local stalk map, and
the open immersion `t₁` identifies its target stalk with the stalk of `X`.
The induced residue-field map is therefore an isomorphism (def-weil-residue-field).
All maps from `X` are the graph sections followed by their projections, so the
identifications are compatible with the original `i₁` and `i₂`. The same open
works for every point; for empty `X` the deleted sets are empty and the open is `P`. -/
theorem etale_fibre_product_pair_refinement
    (S X M₁ M₂ : Scheme.{u}) [IsAffine S] [IsAffine X] [IsAffine M₁] [IsAffine M₂]
    (i₁ : X ⟶ M₁) (i₂ : X ⟶ M₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (e₁ : M₁ ⟶ S) (e₂ : M₂ ⟶ S) (h : i₁ ≫ e₁ = i₂ ≫ e₂) [Etale e₂] :
    ∃ (s : X ⟶ pullback e₁ e₂)
      (t₁ : X ⟶ pullback (pullback.fst e₁ e₂) i₁),
      s = pullback.lift i₁ i₂ h ∧
      t₁ ≫ pullback.fst (pullback.fst e₁ e₂) i₁ = s ∧
      t₁ ≫ pullback.snd (pullback.fst e₁ e₂) i₁ = 𝟙 X ∧
      Etale (pullback.snd (pullback.fst e₁ e₂) i₁) ∧
      IsSeparated (pullback.snd (pullback.fst e₁ e₂) i₁) ∧
      IsOpenImmersion t₁ ∧ IsClosedImmersion t₁ ∧
      IsClosed ((pullback.fst (pullback.fst e₁ e₂) i₁) '' (Set.range t₁)ᶜ) ∧
      (∀ x : X, IsIso (s.residueFieldMap x)) ∧
      ∃ (U₁ : (pullback e₁ e₂).Opens) (s₁ : X ⟶ U₁.toScheme),
        (U₁ : Set (pullback e₁ e₂ : Scheme.{u})) =
          ((pullback.fst (pullback.fst e₁ e₂) i₁) '' (Set.range t₁)ᶜ)ᶜ ∧
        (∀ x : X, s x ∈ U₁) ∧ s₁ ≫ U₁.ι = s ∧
        Etale (U₁.ι ≫ pullback.fst e₁ e₂) ∧
        IsPullback s₁ (𝟙 X) (U₁.ι ≫ pullback.fst e₁ e₂) i₁ ∧
        (Etale e₁ →
          ∃ (t₂ : X ⟶ pullback (pullback.snd e₁ e₂) i₂),
            t₂ ≫ pullback.fst (pullback.snd e₁ e₂) i₂ = s ∧
            t₂ ≫ pullback.snd (pullback.snd e₁ e₂) i₂ = 𝟙 X ∧
            Etale (pullback.snd (pullback.snd e₁ e₂) i₂) ∧
            IsSeparated (pullback.snd (pullback.snd e₁ e₂) i₂) ∧
            IsOpenImmersion t₂ ∧ IsClosedImmersion t₂ ∧
            IsClosed ((pullback.fst (pullback.snd e₁ e₂) i₂) '' (Set.range t₂)ᶜ) ∧
            ∃ (U : (pullback e₁ e₂).Opens) (sU : X ⟶ U.toScheme),
              (U : Set (pullback e₁ e₂ : Scheme.{u})) =
                (((pullback.fst (pullback.fst e₁ e₂) i₁) '' (Set.range t₁)ᶜ) ∪
                  ((pullback.fst (pullback.snd e₁ e₂) i₂) '' (Set.range t₂)ᶜ))ᶜ ∧
              (∀ x : X, s x ∈ U) ∧ sU ≫ U.ι = s ∧
              Etale (U.ι ≫ pullback.fst e₁ e₂) ∧
              Etale (U.ι ≫ pullback.snd e₁ e₂) ∧
              IsPullback sU (𝟙 X) (U.ι ≫ pullback.fst e₁ e₂) i₁ ∧
              IsPullback sU (𝟙 X) (U.ι ≫ pullback.snd e₁ e₂) i₂) := by
  let s : X ⟶ pullback e₁ e₂ := pullback.lift i₁ i₂ h
  have hs₁ : s ≫ pullback.fst e₁ e₂ = i₁ := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd e₁ e₂ = i₂ := pullback.lift_snd _ _ _
  let t₁ := pullback.lift s (𝟙 X) (by simpa using hs₁)
  have ht₁j : t₁ ≫ pullback.fst (pullback.fst e₁ e₂) i₁ = s :=
    pullback.lift_fst _ _ _
  have ht₁q : t₁ ≫ pullback.snd (pullback.fst e₁ e₂) i₁ = 𝟙 X :=
    pullback.lift_snd _ _ _
  obtain ⟨ht₁o, ht₁c⟩ := section_clopen _ t₁ ht₁q
  have hc₁ := complement_closed (pullback.fst (pullback.fst e₁ e₂) i₁) t₁
  let U₁ : (pullback e₁ e₂).Opens := ⟨_, hc₁.isOpen_compl⟩
  have hin₁ (x : X) : s x ∈ (U₁ : Set (pullback e₁ e₂ : Scheme.{u})) := by
    rw [← ht₁j]
    exact section_avoids_complement _ t₁ x
  let s₁ := IsOpenImmersion.lift U₁.ι s (by
    simpa only [Scheme.Opens.range_ι, Set.range_subset_iff] using hin₁)
  have hs₁U : s₁ ≫ U₁.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hpre₁ (z : (pullback (pullback.fst e₁ e₂) i₁ : Scheme.{u})) :
      pullback.fst (pullback.fst e₁ e₂) i₁ z ∈ U₁ ↔ z ∈ Set.range t₁ := by
    change z ∉ (pullback.fst (pullback.fst e₁ e₂) i₁) ⁻¹'
      ((pullback.fst (pullback.fst e₁ e₂) i₁) '' (Set.range t₁)ᶜ) ↔ _
    rw [Set.preimage_image_eq _
      (pullback.fst (pullback.fst e₁ e₂) i₁).isClosedEmbedding.injective]
    exact not_not
  have hsq₁ := section_square _ _ _ _ (IsPullback.of_hasPullback _ _) t₁ ht₁q
    U₁ s₁ (ht₁j.trans hs₁U.symm) hpre₁
  have : SurjectiveOnStalks s := by rw [← ht₁j]; infer_instance
  refine ⟨s, t₁, rfl, ht₁j, ht₁q, inferInstance, inferInstance, ht₁o, ht₁c,
    hc₁, residue_iso_of_surjective_stalks s, U₁, s₁, rfl, hin₁, hs₁U,
    inferInstance, hsq₁, ?_⟩
  intro he₁
  let t₂ := pullback.lift s (𝟙 X) (by simpa using hs₂)
  have ht₂j : t₂ ≫ pullback.fst (pullback.snd e₁ e₂) i₂ = s :=
    pullback.lift_fst _ _ _
  have ht₂q : t₂ ≫ pullback.snd (pullback.snd e₁ e₂) i₂ = 𝟙 X :=
    pullback.lift_snd _ _ _
  obtain ⟨ht₂o, ht₂c⟩ := section_clopen _ t₂ ht₂q
  have hc₂ := complement_closed (pullback.fst (pullback.snd e₁ e₂) i₂) t₂
  let U₂ : (pullback e₁ e₂).Opens := ⟨_, hc₂.isOpen_compl⟩
  have hin₂ (x : X) : s x ∈ (U₂ : Set (pullback e₁ e₂ : Scheme.{u})) := by
    rw [← ht₂j]
    exact section_avoids_complement _ t₂ x
  have hpre₂ (z : (pullback (pullback.snd e₁ e₂) i₂ : Scheme.{u})) :
      pullback.fst (pullback.snd e₁ e₂) i₂ z ∈ U₂ ↔ z ∈ Set.range t₂ := by
    change z ∉ (pullback.fst (pullback.snd e₁ e₂) i₂) ⁻¹'
      ((pullback.fst (pullback.snd e₁ e₂) i₂) '' (Set.range t₂)ᶜ) ↔ _
    rw [Set.preimage_image_eq _
      (pullback.fst (pullback.snd e₁ e₂) i₂).isClosedEmbedding.injective]
    exact not_not
  let U := U₁ ⊓ U₂
  have hin (x : X) : s x ∈ (U : Set (pullback e₁ e₂ : Scheme.{u})) := ⟨hin₁ x, hin₂ x⟩
  let sU := IsOpenImmersion.lift U.ι s (by
    simpa only [Scheme.Opens.range_ι, Set.range_subset_iff] using hin)
  have hsU : sU ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hsqU₁ := section_square _ _ _ _ (IsPullback.of_hasPullback _ _) t₁ ht₁q
    U sU (ht₁j.trans hsU.symm) (by
      intro z
      constructor
      · exact fun hz ↦ (hpre₁ z).mp hz.1
      · rintro ⟨x, rfl⟩
        simpa [← Scheme.Hom.comp_apply, ht₁j] using hin x)
  have hsqU₂ := section_square _ _ _ _ (IsPullback.of_hasPullback _ _) t₂ ht₂q
    U sU (ht₂j.trans hsU.symm) (by
      intro z
      constructor
      · exact fun hz ↦ (hpre₂ z).mp hz.2
      · rintro ⟨x, rfl⟩
        simpa [← Scheme.Hom.comp_apply, ht₂j] using hin x)
  refine ⟨t₂, ht₂j, ht₂q, inferInstance, inferInstance, ht₂o, ht₂c, hc₂,
    U, sU, ?_, hin, hsU, inferInstance, inferInstance, hsqU₁, hsqU₂⟩
  exact (Set.compl_union _ _).symm

end AlgebraicGeometry
