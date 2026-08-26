/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Complements on separated morphisms

This file collects complements on separated morphisms of schemes.

## The diagonal of a separated morphism locally of finite presentation

For a separated morphism the diagonal is a closed immersion. Combined with
`AlgebraicGeometry.locallyOfFinitePresentation_diagonal` this shows that the diagonal of a
separated morphism locally of finite presentation is a closed immersion of finite presentation
(`AlgebraicGeometry.Scheme.Hom.diagonal_isClosedImmersion_finitePresentation`).

## Separatedness from an open cover of the source

We prove the criterion of separatedness over an open cover (Stacks Project Tag 0F3U):
`w : W ⟶ S` is separated as soon as `W` has an open cover `𝒰` for which every overlap
morphism `𝒰ᵢ ×_W 𝒰ⱼ ⟶ 𝒰ᵢ ×_S 𝒰ⱼ` is a closed immersion
(`AlgebraicGeometry.IsSeparated.of_openCover`), together with its two-element special
case `AlgebraicGeometry.IsSeparated.of_two_open_cover`, in which the diagonal overlaps
are supplied by separatedness of `T₁ ⟶ S` and `T₂ ⟶ S`.

The proof covers `W ×_S W` by the chart opens `𝒰ᵢ ×_S 𝒰ⱼ` and identifies the
restriction of the diagonal over such a chart with the overlap morphism
(`AlgebraicGeometry.diagonalRestrictChartArrowIso`); over the diagonal charts that
morphism is the closed-immersion diagonal of `𝒰ᵢ ⟶ S`
(`AlgebraicGeometry.isClosedImmersion_pullback_map_self`), and the two mixed charts of
a two-element cover are exchanged by the symmetry isomorphism
(`AlgebraicGeometry.pullback_map_symmetry`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The diagonal of a separated morphism of finite presentation is a closed immersion of
finite presentation.**

Mathlib has no bundled class for "of finite presentation"; a morphism is of finite presentation
if it is locally of finite presentation, quasi-compact and quasi-separated. -/
theorem Scheme.Hom.diagonal_isClosedImmersion_finitePresentation [IsSeparated f]
    [LocallyOfFinitePresentation f] :
    IsClosedImmersion (pullback.diagonal f) ∧
      LocallyOfFinitePresentation (pullback.diagonal f) ∧
      QuasiCompact (pullback.diagonal f) ∧ QuasiSeparated (pullback.diagonal f) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end Diagonal

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
      have hr : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := by
        rw [Scheme.Pullback.range_fst_comp]
        exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      exact hr
    · rintro ⟨t, ht⟩
      have hx : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := ⟨t, ht⟩
      rw [Scheme.Pullback.range_fst_comp] at hx
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      have hr : pullback.diagonal w x ∈
          Set.range (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S)
            (by simp) (by simp)) := by
        rw [Scheme.Pullback.range_map]
        refine ⟨⟨x₁, ?_⟩, ⟨x₂, ?_⟩⟩
        · rw [hΔfst]
          exact hx₁
        · rw [hΔsnd]
          exact hx₂
      exact hr

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

/-- **Separatedness is detected on an open cover of the source** (Stacks Project
Tag 0F3U): if `𝒰` is an open cover of `W` and every canonical overlap morphism
`𝒰ᵢ ×_W 𝒰ⱼ ⟶ 𝒰ᵢ ×_S 𝒰ⱼ` is a closed immersion, then `w : W ⟶ S` is separated. The
diagonal cases `i = j` say exactly that `𝒰ᵢ ⟶ S` is separated, see
`AlgebraicGeometry.isClosedImmersion_pullback_map_self`. -/
theorem IsSeparated.of_openCover (𝒰 : W.OpenCover)
    (hd : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.map (𝒰.f i) (𝒰.f j)
      (𝒰.f i ≫ w) (𝒰.f j ≫ w) (𝟙 (𝒰.X i)) (𝟙 (𝒰.X j)) w (by simp) (by simp))) :
    IsSeparated w := by
  constructor
  -- the product charts `𝒰ᵢ ×_S 𝒰ⱼ` of `W ×_S W`
  let c : 𝒰.I₀ × 𝒰.I₀ → (pullback w w).Opens := fun p ↦
    (pullback.map (𝒰.f p.1 ≫ w) (𝒰.f p.2 ≫ w) w w (𝒰.f p.1) (𝒰.f p.2) (𝟙 S)
      (by simp) (by simp)).opensRange
  have hO : (⨆ p : 𝒰.I₀ × 𝒰.I₀, c p) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨(𝒰.idx (pullback.fst w w z), 𝒰.idx (pullback.snd w w z)), ?_⟩
    simp only [c, Scheme.Hom.mem_opensRange, ← Set.mem_range, Scheme.Pullback.range_map]
    exact ⟨𝒰.covers _, 𝒰.covers _⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) c hO]
  rintro ⟨i, j⟩
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (diagonalRestrictChartArrowIso w (𝒰.f i) (𝒰.f j))).mpr (hd i j)

/-- **Separatedness from a two-open cover** (Stacks Project Tag 0F3U; blueprint:
`lemma:nagata-separated-two-open-cover`): let `W = T₁ ∪ T₂` be a union of two open
subschemes over `S` such that each `Tᵢ ⟶ S` is separated and the canonical overlap
morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` is a closed immersion. Then `W ⟶ S` is separated.
This is the two-element case of `AlgebraicGeometry.IsSeparated.of_openCover`. -/
theorem IsSeparated.of_two_open_cover
    (hcov : Set.range j₁ ∪ Set.range j₂ = Set.univ)
    [IsSeparated (j₁ ≫ w)] [IsSeparated (j₂ ≫ w)]
    (hd : IsClosedImmersion (pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w
      (by simp) (by simp))) :
    IsSeparated w := by
  -- the remaining mixed chart is the given one up to the symmetry of the fibre products
  have h21 : IsClosedImmersion (pullback.map j₂ j₁ (j₂ ≫ w) (j₁ ≫ w) (𝟙 T₂) (𝟙 T₁) w
      (by simp) (by simp)) := by
    have := hd
    rw [pullback_map_symmetry w]
    infer_instance
  refine IsSeparated.of_openCover w (Scheme.Cover.mkOfCovers WalkingPair
    (fun k ↦ WalkingPair.casesOn k T₁ T₂) (fun k ↦ WalkingPair.casesOn k j₁ j₂)
    (fun x ↦ ?_) (fun k ↦ by cases k <;> infer_instance)) (fun i j ↦ ?_)
  · have hx : x ∈ Set.range j₁ ∪ Set.range j₂ := by
      rw [hcov]
      trivial
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hx
    exacts [⟨WalkingPair.left, y, hy⟩, ⟨WalkingPair.right, y, hy⟩]
  · cases i <;> cases j
    exacts [isClosedImmersion_pullback_map_self w j₁, hd, h21,
      isClosedImmersion_pullback_map_self w j₂]

end TwoOpenCover

end AlgebraicGeometry
