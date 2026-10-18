/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Hyperplane

/-!
# The total space of `𝒪(1)` on projective space

The total space of the line bundle `𝒪(1)` on `ℙ(n; S)` is the open subscheme
`W = ⋃ᵢ D₊(Tᵢ)` of `ℙ(Option n; S)`, the complement of the point `[0 : ⋯ : 0 : 1]`, with the
projection `[x : t] ↦ [x]` (`AlgebraicGeometry.ProjectiveSpace.twistBundleπ`); its zero section is
the hyperplane embedding.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover.restrict`: the restriction of a coordinate cover to an
  open subscheme.
- `AlgebraicGeometry.ProjectiveSpace.twistBundleOpen`: the open `W`.
- `AlgebraicGeometry.ProjectiveSpace.twistBundleπ`: the projection `W ⟶ ℙ(n; S)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι) (W : X.Opens)

/-- The restriction of a coordinate cover of `X` to an open subscheme `W`. -/
noncomputable def restrict : W.toScheme.CoordinateCover ι where
  U i := W.ι ⁻¹ᵁ 𝒟.U i
  ratio i j := W.ι.app (𝒟.U i) (𝒟.ratio i j)
  ratio_self i := by simp [𝒟.ratio_self]
  basicOpen_ratio i j := by
    rw [← Scheme.preimage_basicOpen, 𝒟.basicOpen_ratio]
    rfl
  ratio_mul i j l := by
    have h₁ := congrArg (fun f ↦ f (𝒟.ratio i l)) (W.ι.naturality
      (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op)
    have h₂ := congrArg (fun f ↦ f (𝒟.ratio i j)) (W.ι.naturality
      (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op)
    have h₃ := congrArg (fun f ↦ f (𝒟.ratio j l)) (W.ι.naturality
      (homOfLE (inf_le_right : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U j)).op)
    simp only [CommRingCat.comp_apply] at h₁ h₂ h₃
    have := congrArg (W.ι.app (𝒟.U i ⊓ 𝒟.U j)) (𝒟.ratio_mul i j l)
    rw [map_mul] at this
    exact h₁.symm.trans (this.trans (by rw [h₂, h₃]; rfl))
  iSup_U := by
    rw [← Scheme.Hom.preimage_iSup, 𝒟.iSup_U]
    rfl

@[simp]
lemma restrict_U (i : ι) : (𝒟.restrict W).U i = W.ι ⁻¹ᵁ 𝒟.U i := rfl

end Scheme.CoordinateCover

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Type u) (S : Scheme.{u})

/-- The open `W = ⋃ᵢ D₊(Tᵢ) ⊆ ℙ(Option n; S)`, the complement of `[0 : ⋯ : 0 : 1]`: the total
space of `𝒪(1)` on `ℙ(n; S)`. -/
noncomputable def twistBundleOpen : ℙ(Option n; S).Opens :=
  ⨆ i : n, standardOpen (Option n) S (some i)

/-- The standard coordinate cover of `ℙ(Option n; S)` restricted to `W`. -/
noncomputable def twistBundleCover₀ : (twistBundleOpen n S).toScheme.CoordinateCover (Option n) :=
  (standardCoordinateCover (Option n) S).restrict (twistBundleOpen n S)

lemma iSup_nonvanishing_twistBundleCover₀ :
    ⨆ i : n, ((twistBundleCover₀ n S).coord (some i)).nonvanishing = ⊤ := by
  simp only [nonvanishing_coord, twistBundleCover₀, Scheme.CoordinateCover.restrict_U,
    standardCoordinateCover_U]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

/-- The coordinate cover of `W` by the opens `W ∩ D₊(Tᵢ)`, `i : n`. -/
noncomputable def twistBundleCover : (twistBundleOpen n S).toScheme.CoordinateCover n :=
  Scheme.CoordinateCover.ofSections (fun i ↦ (twistBundleCover₀ n S).coord (some i)) some
    (fun _ ↦ (nonvanishing_coord _ _).le) (iSup_nonvanishing_twistBundleCover₀ n S)

@[simp]
lemma twistBundleCover_U (i : n) :
    (twistBundleCover n S).U i = (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) :=
  nonvanishing_coord _ _

lemma twistBundleCover_ratio (i a : n) :
    (twistBundleCover n S).ratio i a =
      (twistBundleOpen n S).toScheme.presheaf.map (homOfLE (nonvanishing_coord _ _).le).op
        ((twistBundleCover₀ n S).ratio (some i) (some a)) := by
  have hu : (Scheme.CoordinateCover.isUnit_map_s
      (fun i ↦ (twistBundleCover₀ n S).coord (some i)) some
      (fun _ ↦ (nonvanishing_coord _ _).le) i).unit = 1 := by
    ext
    simp [Scheme.CoordinateCover.coord_s, (twistBundleCover₀ n S).ratio_self]
  simp only [twistBundleCover, Scheme.CoordinateCover.ofSections, hu, inv_one, Units.val_one,
    mul_one, Scheme.CoordinateCover.coord_s]

lemma span_twistBundleCover_coord (i : n) :
    Ideal.span (Set.range fun a ↦ ((twistBundleCover n S).coord a).s i) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) ?_
  simp [(twistBundleCover n S).ratio_self i]

/-- The projection `W ⟶ ℙ(n; S)`, `[x : t] ↦ [x]`, of the total space of `𝒪(1)`. -/
noncomputable def twistBundleπ : (twistBundleOpen n S).toScheme ⟶ ℙ(n; S) :=
  Scheme.CoordinateCover.hom (fun i ↦ (twistBundleCover n S).coord i)
    (span_twistBundleCover_coord n S) ((twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S)

@[reassoc (attr := simp)]
lemma twistBundleπ_over :
    twistBundleπ n S ≫ ℙ(n; S) ↘ S = (twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S :=
  Scheme.CoordinateCover.hom_over _ _ _

/-- The preimage of `D₊(Tᵢ)` under the projection is `W ∩ D₊(Tᵢ)`. -/
lemma twistBundleπ_preimage_standardOpen (i : n) :
    twistBundleπ n S ⁻¹ᵁ standardOpen n S i =
      (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := by
  rw [twistBundleπ, Scheme.CoordinateCover.preimage_hom_standardOpen, nonvanishing_coord,
    twistBundleCover_U]

lemma range_hyperplane_subset_twistBundleOpen :
    Set.range (hyperplane n S).base ⊆ Set.range (twistBundleOpen n S).ι.base := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen n S).ge (Set.mem_univ x))
  rw [Scheme.Opens.range_ι]
  have hx : x ∈ hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i) := by
    rw [hyperplane_preimage_standardOpen_some]
    exact hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩

/-- The zero section `ℙ(n; S) ⟶ W` of the total space of `𝒪(1)`: the hyperplane embedding. -/
noncomputable def twistBundleZero : ℙ(n; S) ⟶ (twistBundleOpen n S).toScheme :=
  IsOpenImmersion.lift (twistBundleOpen n S).ι (hyperplane n S)
    (range_hyperplane_subset_twistBundleOpen n S)

@[reassoc (attr := simp)]
lemma twistBundleZero_ι : twistBundleZero n S ≫ (twistBundleOpen n S).ι = hyperplane n S :=
  IsOpenImmersion.lift_fac _ _ _

lemma span_coordRatio_standardOpen (i : n) :
    Ideal.span (Set.range fun a ↦ (standardOpen n S i).topIso.inv (coordRatio n S i a)) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) ?_
  dsimp only
  rw [← standardCoordinateCover_ratio, (standardCoordinateCover n S).ratio_self, map_one]
  exact isUnit_one

/-- The inclusion of the standard open `D₊(Tᵢ)` is the morphism defined by the ratios
`Tₐ / Tᵢ`. -/
lemma ι_eq_homOfSections (i : n) :
    (standardOpen n S i).ι = homOfSections ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun a ↦ (standardOpen n S i).topIso.inv (coordRatio n S i a))
      (span_coordRatio_standardOpen n S i) := by
  rw [homOfSections_eq_of_eq_one _ _ _ i (by
    rw [← standardCoordinateCover_ratio, (standardCoordinateCover n S).ratio_self, map_one])]
  have : AffineSpace.homOfVector ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun j : {j : n // j ≠ i} ↦ (standardOpen n S i).topIso.inv (coordRatio n S i j.1)) =
      (standardOpenIso n S i).hom := by
    refine AffineSpace.hom_ext ?_ fun j ↦ ?_
    · rw [AffineSpace.homOfVector_over, standardOpenIso_hom_over]
    · rw [AffineSpace.homOfVector_appTop_coord, standardOpenIso_hom_appTop_coord]
  rw [this, Iso.hom_inv_id_assoc]

/-- The zero section is a section of the projection.

Not proved here. On the chart `D₊(Tᵢ)` of `ℙ(n; S)` both sides are `homOfSections` of the ratios
`Tⱼ / Tᵢ` (`AlgebraicGeometry.ProjectiveSpace.comp_homOfSections`,
`Scheme.CoordinateCover.ι_hom`): the ratios of `twistBundleCover` are the restrictions of
`T_{some j} / T_{some i}`, which the hyperplane embedding pulls back to `Tⱼ / Tᵢ`. -/
lemma twistBundleZero_comp_π : twistBundleZero n S ≫ twistBundleπ n S = 𝟙 ℙ(n; S) := by
  sorry

end ProjectiveSpace

end AlgebraicGeometry
