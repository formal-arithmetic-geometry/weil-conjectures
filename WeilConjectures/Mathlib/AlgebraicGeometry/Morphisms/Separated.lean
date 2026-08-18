/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Separatedness from a two-open cover

We prove the criterion of separatedness over a two-open cover (Stacks Project
Tag 0F3U): if `W = T₁ ∪ T₂` is a union of two opens over `S` such that each `Tᵢ ⟶ S`
is separated and the overlap morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` is a closed immersion,
then `W ⟶ S` is separated.

The proof covers `W ×_S W` by the four chart opens `T_a ×_S T_b` and identifies the
restriction of the diagonal over the chart `T_a ×_S T_b` with the canonical morphism
`T_a ×_W T_b ⟶ T_a ×_S T_b` (`AlgebraicGeometry.diagonalRestrictChartArrowIso`); over
the diagonal charts this morphism is the closed-immersion diagonal of `T_a ⟶ S`
(`AlgebraicGeometry.isClosedImmersion_pullback_map_self`), and over the mixed charts
it is the overlap morphism up to the symmetry isomorphism
(`AlgebraicGeometry.pullback_map_symmetry`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {W S : Scheme.{u}} (w : W ⟶ S)

section TwoOpenCover

variable {T₁ T₂ : Scheme.{u}} (j₁ : T₁ ⟶ W) (j₂ : T₂ ⟶ W)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- The restriction of the diagonal of `w : W ⟶ S` over the chart
`T₁ ×_S T₂ ⊆ W ×_S W` attached to a pair of open immersions `jᵢ : Tᵢ ⟶ W` is the
canonical morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂`. -/
def diagonalRestrictChartArrowIso :
    Arrow.mk (pullback.diagonal w ∣_
        (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S) (by simp) (by simp)).opensRange) ≅
      Arrow.mk (pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w
        (by simp) (by simp)) := by
  refine morphismRestrictArrowIso (pullback.diagonal w)
    (e := pullback.fst j₁ j₂ ≫ j₁) _ ?_ ?_
  · apply pullback.hom_ext
    · simp
    · simp [pullback.condition]
  · have hΔfst : ∀ y : W, (pullback.fst w w) (pullback.diagonal w y) = y := fun y ↦ by
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
      simp
    have hΔsnd : ∀ y : W, (pullback.snd w w) (pullback.diagonal w y) = y := fun y ↦ by
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
      simp
    ext x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      Scheme.Hom.mem_opensRange]
    constructor
    · rintro ⟨t, ht⟩
      have hx : pullback.diagonal w x ∈
          Set.range (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S)
            (by simp) (by simp)) := ⟨t, ht⟩
      rw [Scheme.Pullback.range_map] at hx
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      rw [hΔfst] at hx₁
      rw [hΔsnd] at hx₂
      have : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := by
        rw [Scheme.Pullback.range_fst_comp]
        exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      exact this
    · rintro ⟨t, ht⟩
      have hx : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := ⟨t, ht⟩
      rw [Scheme.Pullback.range_fst_comp] at hx
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      have : pullback.diagonal w x ∈
          Set.range (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S)
            (by simp) (by simp)) := by
        rw [Scheme.Pullback.range_map]
        exact ⟨⟨x₁, by rw [hΔfst]; exact hx₁⟩, ⟨x₂, by rw [hΔsnd]; exact hx₂⟩⟩
      exact this

variable {j₁ j₂}

/-- Over a diagonal chart, the canonical morphism `T ×_W T ⟶ T ×_S T` is the diagonal
of `T ⟶ S` up to the diagonal isomorphism of the monomorphism `j : T ⟶ W`; it is a
closed immersion whenever `T ⟶ S` is separated. -/
theorem isClosedImmersion_pullback_map_self {T : Scheme.{u}} (j : T ⟶ W) [Mono j]
    [IsSeparated (j ≫ w)] :
    IsClosedImmersion (pullback.map j j (j ≫ w) (j ≫ w) (𝟙 T) (𝟙 T) w
      (by simp) (by simp)) := by
  have hdiag : pullback.map j j (j ≫ w) (j ≫ w) (𝟙 T) (𝟙 T) w (by simp) (by simp) =
      inv (pullback.diagonal j) ≫ pullback.diagonal (j ≫ w) := by
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext <;> simp
  rw [hdiag]
  infer_instance

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂] in
/-- The mixed chart morphisms `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` and `T₂ ×_W T₁ ⟶ T₂ ×_S T₁` are
related by the symmetry isomorphisms of the fibre products. -/
theorem pullback_map_symmetry :
    pullback.map j₂ j₁ (j₂ ≫ w) (j₁ ≫ w) (𝟙 T₂) (𝟙 T₁) w (by simp) (by simp) =
      (pullbackSymmetry j₂ j₁).hom ≫
        pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w (by simp) (by simp) ≫
        (pullbackSymmetry (j₁ ≫ w) (j₂ ≫ w)).hom := by
  apply pullback.hom_ext <;> simp

variable (j₁ j₂)

/-- **Separatedness from a two-open cover** (Stacks Project Tag 0F3U; blueprint:
`lemma:nagata-separated-two-open-cover`): let `W = T₁ ∪ T₂` be a union of two open
subschemes over `S` such that each `Tᵢ ⟶ S` is separated and the canonical overlap
morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` is a closed immersion. Then `W ⟶ S` is separated. -/
theorem IsSeparated.of_two_open_cover
    (hcov : Set.range j₁ ∪ Set.range j₂ = Set.univ)
    [IsSeparated (j₁ ≫ w)] [IsSeparated (j₂ ≫ w)]
    (hd : IsClosedImmersion (pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w
      (by simp) (by simp))) :
    IsSeparated w := by
  constructor
  -- the four product charts of `W ×_S W`
  have hmem : ∀ {A B : Scheme.{u}} (i₁ : A ⟶ W) (i₂ : B ⟶ W) (_ : IsOpenImmersion i₁)
      (_ : IsOpenImmersion i₂) (z : ↑(pullback w w)),
      pullback.fst w w z ∈ Set.range i₁ → pullback.snd w w z ∈ Set.range i₂ →
      z ∈ (pullback.map (i₁ ≫ w) (i₂ ≫ w) w w i₁ i₂ (𝟙 S)
        (by simp) (by simp)).opensRange := by
    intro A B i₁ i₂ _ _ z h₁ h₂
    have : z ∈ Set.range (pullback.map (i₁ ≫ w) (i₂ ≫ w) w w i₁ i₂ (𝟙 S)
        (by simp) (by simp)) := by
      rw [Scheme.Pullback.range_map]
      exact ⟨h₁, h₂⟩
    exact this
  classical
  let c : Fin 2 × Fin 2 → (pullback w w).Opens := fun p ↦
    if p = (0, 0) then
      (pullback.map (j₁ ≫ w) (j₁ ≫ w) w w j₁ j₁ (𝟙 S) (by simp) (by simp)).opensRange
    else if p = (0, 1) then
      (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S) (by simp) (by simp)).opensRange
    else if p = (1, 0) then
      (pullback.map (j₂ ≫ w) (j₁ ≫ w) w w j₂ j₁ (𝟙 S) (by simp) (by simp)).opensRange
    else
      (pullback.map (j₂ ≫ w) (j₂ ≫ w) w w j₂ j₂ (𝟙 S) (by simp) (by simp)).opensRange
  have hO : (⨆ p : Fin 2 × Fin 2, c p) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have h₁ : pullback.fst w w z ∈ Set.range j₁ ∪ Set.range j₂ := hcov ▸ Set.mem_univ _
    have h₂ : pullback.snd w w z ∈ Set.range j₁ ∪ Set.range j₂ := hcov ▸ Set.mem_univ _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain h₁ | h₁ := h₁ <;> obtain h₂ | h₂ := h₂
    · exact ⟨(0, 0), by simpa [c] using hmem j₁ j₁ ‹_› ‹_› z h₁ h₂⟩
    · exact ⟨(0, 1), by simpa [c] using hmem j₁ j₂ ‹_› ‹_› z h₁ h₂⟩
    · exact ⟨(1, 0), by simpa [c] using hmem j₂ j₁ ‹_› ‹_› z h₁ h₂⟩
    · exact ⟨(1, 1), by simpa [c] using hmem j₂ j₂ ‹_› ‹_› z h₁ h₂⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) c hO]
  have h21 : IsClosedImmersion (pullback.map j₂ j₁ (j₂ ≫ w) (j₁ ≫ w) (𝟙 T₂) (𝟙 T₁) w
      (by simp) (by simp)) := by
    have := hd
    rw [pullback_map_symmetry w]
    infer_instance
  rintro ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp only [c]
  · exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (diagonalRestrictChartArrowIso w j₁ j₁)).mpr (isClosedImmersion_pullback_map_self w j₁)
  · exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (diagonalRestrictChartArrowIso w j₁ j₂)).mpr hd
  · exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (diagonalRestrictChartArrowIso w j₂ j₁)).mpr h21
  · exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (diagonalRestrictChartArrowIso w j₂ j₂)).mpr (isClosedImmersion_pullback_map_self w j₂)

end TwoOpenCover

end AlgebraicGeometry
