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

/-- **The zero section is a section of the projection.**
On the chart `D₊(Tᵢ)` of `ℙ(n; S)` both sides are `homOfSections` of the ratios
`Tⱼ / Tᵢ` (`AlgebraicGeometry.ProjectiveSpace.comp_homOfSections`,
`Scheme.CoordinateCover.ι_hom`): the ratios of `twistBundleCover` are the restrictions of
`T_{some j} / T_{some i}`, which the hyperplane embedding pulls back to `Tⱼ / Tᵢ`. -/
lemma twistBundleZero_comp_π : twistBundleZero n S ≫ twistBundleπ n S = 𝟙 ℙ(n; S) := by
  refine Scheme.Opens.hom_ext_of_iSup_eq_top (fun i ↦ standardOpen n S i) (iSup_standardOpen n S)
    _ _ fun i ↦ ?_
  have hr : Set.range ((standardOpen n S i).ι ≫ twistBundleZero n S).base ⊆
      Set.range ((twistBundleCover n S).U i).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, twistBundleCover_U]
    have hx : x.1 ∈ hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i) := by
      rw [hyperplane_preimage_standardOpen_some]
      exact x.2
    change ((standardOpen n S i).ι ≫ twistBundleZero n S ≫ (twistBundleOpen n S).ι).base x ∈
      standardOpen (Option n) S (some i)
    rw [twistBundleZero_ι]
    exact hx
  let c := IsOpenImmersion.lift _ _ hr
  have hc : c ≫ ((twistBundleCover n S).U i).ι = (standardOpen n S i).ι ≫ twistBundleZero n S :=
    IsOpenImmersion.lift_fac _ _ _
  have hh := Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover n S)
    (hyperplaneSections n S) (span_hyperplaneSections n S) (ℙ(n; S) ↘ S) i
  rw [Scheme.CoordinateCover.localHom] at hh
  rw [← Category.assoc, ← hc, Category.assoc, twistBundleπ, Scheme.CoordinateCover.ι_hom,
    Scheme.CoordinateCover.localHom, comp_homOfSections, Category.comp_id]
  conv_rhs => rw [ι_eq_homOfSections n S i]
  congr 1
  · rw [← Category.assoc c, hc, Category.assoc, twistBundleZero_ι_assoc, hyperplane_over]
  · funext a
    rw [Scheme.CoordinateCover.coord_s, twistBundleCover_ratio]
    have e₁ : ((twistBundleCover n S).U i).topIso.inv =
        ((twistBundleCover n S).U i).ι.appLE ((twistBundleCover n S).U i) ⊤
          (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : c.appTop = c.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hV : (twistBundleCover n S).U i ≤
        (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := le_of_eq (by simp)
    have e₃ : (twistBundleOpen n S).toScheme.presheaf.map
        (homOfLE (nonvanishing_coord _ _).le).op ((twistBundleCover₀ n S).ratio (some i) (some a)) =
        (twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i))
          ((twistBundleCover n S).U i) hV (coordRatio (Option n) S (some i) (some a)) := rfl
    rw [e₁, e₂, e₃, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [appLE_eq_of_eq (show (c ≫ ((twistBundleCover n S).U i).ι) ≫ (twistBundleOpen n S).ι =
      (standardOpen n S i).ι ≫ hyperplane n S by rw [hc, Category.assoc, twistBundleZero_ι])]
    have hh' : (standardOpen n S i).ι ≫ hyperplane n S = homOfSections
        ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
        (fun a ↦ (standardOpen n S i).topIso.inv ((hyperplaneSections n S a).s i))
        (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections n S) i) := hh
    rw [appLE_eq_of_eq hh']
    exact (homOfSections_appLE_coordRatio (S := S) ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun a ↦ (standardOpen n S i).topIso.inv ((hyperplaneSections n S a).s i))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections n S) i)
      (hyperplaneSections_some_s_self n S i) (some a) _).trans rfl

/-- The fibre coordinate `T_∗ / Tᵢ` of the total space over the chart `D₊(Tᵢ)`. -/
noncomputable def twistBundleFiberCoord (i : n) :
    Γ((twistBundleπ n S ⁻¹ᵁ standardOpen n S i).toScheme, ⊤) :=
  (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).topIso.inv
    ((twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i)) _
      (twistBundleπ_preimage_standardOpen n S i).le (coordRatio (Option n) S (some i) none))

/-- The chart `π⁻¹(D₊(Tᵢ)) ⟶ 𝔸¹_{D₊(Tᵢ)}` of the total space, `[x : t] ↦ ([x], t / xᵢ)`. It is
over `D₊(Tᵢ)` by construction (`AlgebraicGeometry.ProjectiveSpace.twistBundleChartHom_over`).

To do (for `VectorBundle 1 (twistBundleπ n S)`): it is an isomorphism, with inverse the morphism
`𝔸¹_{D₊(Tᵢ)} ⟶ D₊(T_{some i}) ⊆ W` defined by the sections `(Tₖ / Tᵢ, t)`; it carries the zero
section to the zero section; and the fibre coordinates satisfy
`T_∗ / Tⱼ = (Tᵢ / Tⱼ) (T_∗ / Tᵢ)` (`AlgebraicGeometry.ProjectiveSpace.map_coordRatio_eq_mul`). -/
noncomputable def twistBundleChartHom (i : n) :
    (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).toScheme ⟶
      𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) :=
  AffineSpace.homOfVector (twistBundleπ n S ∣_ standardOpen n S i)
    (fun _ ↦ twistBundleFiberCoord n S i)

@[reassoc (attr := simp)]
lemma twistBundleChartHom_over (i : n) :
    twistBundleChartHom n S i ≫ 𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ↘ _ =
      twistBundleπ n S ∣_ standardOpen n S i :=
  AffineSpace.homOfVector_over _ _

/-- The sections `(Tₖ / Tᵢ, t)` on `𝔸¹_{D₊(Tᵢ)}` defining the inverse of the chart. -/
noncomputable def twistBundleChartInvSections (i : n) :
    Option n → Γ(𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme), ⊤)
  | some k => (𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ↘ _).appTop
      ((standardOpen n S i).topIso.inv (coordRatio n S i k))
  | none => AffineSpace.coord _ ⟨0⟩

lemma twistBundleChartInvSections_some_self (i : n) :
    twistBundleChartInvSections n S i (some i) = 1 := by
  simp only [twistBundleChartInvSections]
  rw [← standardCoordinateCover_ratio, (standardCoordinateCover n S).ratio_self, map_one,
    map_one]

lemma span_twistBundleChartInvSections (i : n) :
    Ideal.span (Set.range (twistBundleChartInvSections n S i)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨some i, rfl⟩)
    (by rw [twistBundleChartInvSections_some_self]; exact isUnit_one)

/-- The inverse of the chart, as a morphism to `ℙ(Option n; S)`: `(x, t) ↦ [x : t]`. -/
noncomputable def twistBundleChartInvAux (i : n) :
    𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ⟶ ℙ(Option n; S) :=
  homOfSections (𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ↘ _ ≫
      (standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
    (twistBundleChartInvSections n S i) (span_twistBundleChartInvSections n S i)

lemma range_twistBundleChartInvAux (i : n) :
    Set.range (twistBundleChartInvAux n S i).base ⊆
      Set.range ((twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ (twistBundleOpen n S).ι).base := by
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ twistBundleChartInvAux n S i ⁻¹ᵁ standardOpen (Option n) S (some i) := by
    rw [twistBundleChartInvAux, homOfSections_preimage_standardOpen,
      twistBundleChartInvSections_some_self, Scheme.basicOpen_one]
    trivial
  have hW : (twistBundleChartInvAux n S i).base x ∈ twistBundleOpen n S :=
    TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩
  have hU : (⟨_, hW⟩ : (twistBundleOpen n S).toScheme) ∈
      twistBundleπ n S ⁻¹ᵁ standardOpen n S i := by
    rw [twistBundleπ_preimage_standardOpen]
    exact hx
  exact ⟨⟨_, hU⟩, rfl⟩

/-- The inverse of the chart `𝔸¹_{D₊(Tᵢ)} ⟶ π⁻¹(D₊(Tᵢ))`. -/
noncomputable def twistBundleChartInv (i : n) :
    𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ⟶
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).toScheme :=
  IsOpenImmersion.lift _ _ (range_twistBundleChartInvAux n S i)

@[reassoc (attr := simp)]
lemma twistBundleChartInv_ι (i : n) :
    twistBundleChartInv n S i ≫ (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫
      (twistBundleOpen n S).ι = twistBundleChartInvAux n S i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The projection pulls back the ratio `Tₖ / Tᵢ` on `D₊(Tᵢ)` to the ratio `T_{some k} / T_{some i}`
on `W ∩ D₊(T_{some i})`. -/
lemma twistBundleπ_appLE_coordRatio (i k : n) (h h') :
    (twistBundleπ n S).appLE (standardOpen n S i) ((twistBundleCover n S).U i) h
        (coordRatio n S i k) =
      (twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i))
        ((twistBundleCover n S).U i) h' (coordRatio (Option n) S (some i) (some k)) := by
  apply ((twistBundleCover n S).U i).topIso.commRingCatIsoToRingEquiv.symm.injective
  change ((twistBundleCover n S).U i).topIso.inv _ = ((twistBundleCover n S).U i).topIso.inv _
  have e₁ : ((twistBundleCover n S).U i).topIso.inv =
      ((twistBundleCover n S).U i).ι.appLE ((twistBundleCover n S).U i) ⊤
        (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have hh := Scheme.CoordinateCover.ι_hom (fun a ↦ (twistBundleCover n S).coord a)
    (span_twistBundleCover_coord n S) ((twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S) i
  rw [Scheme.CoordinateCover.localHom] at hh
  conv_lhs => rw [e₁, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hh' : ((twistBundleCover n S).U i).ι ≫ twistBundleπ n S = homOfSections
      (((twistBundleCover n S).U i).ι ≫ (twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S)
      (fun a ↦ ((twistBundleCover n S).U i).topIso.inv (((twistBundleCover n S).coord a).s i))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleCover_coord n S) i) := hh
  rw [appLE_eq_of_eq hh']
  refine (homOfSections_appLE_coordRatio (S := S) _
    (fun a ↦ ((twistBundleCover n S).U i).topIso.inv (((twistBundleCover n S).coord a).s i))
    (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleCover_coord n S) i)
    (by simp [(twistBundleCover n S).ratio_self]) k _).trans ?_
  dsimp only
  rw [Scheme.CoordinateCover.coord_s, twistBundleCover_ratio]
  rfl

/-- The inverse of the chart pulls back the fibre coordinate `T_∗ / Tᵢ` to the coordinate `t` of
the affine line. -/
lemma twistBundleChartInv_appTop_fiberCoord (i : n) :
    (twistBundleChartInv n S i).appTop (twistBundleFiberCoord n S i) =
      AffineSpace.coord _ ⟨0⟩ := by
  have e₁ : (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).topIso.inv =
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι.appLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i)
        ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have e₂ : (twistBundleChartInv n S i).appTop = (twistBundleChartInv n S i).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [twistBundleFiberCoord, e₁, e₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_eq_of_eq (show (twistBundleChartInv n S i ≫
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι) ≫ (twistBundleOpen n S).ι =
      twistBundleChartInvAux n S i by rw [Category.assoc, twistBundleChartInv_ι])]
  exact (homOfSections_appLE_coordRatio (S := S) _ (twistBundleChartInvSections n S i)
    (span_twistBundleChartInvSections n S i) (twistBundleChartInvSections_some_self n S i)
    none _).trans rfl

/-- The inverse of the chart lies over `D₊(Tᵢ)`. -/
lemma twistBundleChartInv_comp_π (i : n) :
    twistBundleChartInv n S i ≫ (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ twistBundleπ n S =
      𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) ↘ _ ≫ (standardOpen n S i).ι := by
  have hle : twistBundleπ n S ⁻¹ᵁ standardOpen n S i ≤ (twistBundleCover n S).U i := by
    rw [twistBundleπ_preimage_standardOpen, twistBundleCover_U]
  have hh := Scheme.CoordinateCover.ι_hom (fun a ↦ (twistBundleCover n S).coord a)
    (span_twistBundleCover_coord n S) ((twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S) i
  have hh' : ((twistBundleCover n S).U i).ι ≫ twistBundleπ n S = homOfSections
      (((twistBundleCover n S).U i).ι ≫ (twistBundleOpen n S).ι ≫ ℙ(Option n; S) ↘ S)
      (fun a ↦ ((twistBundleCover n S).U i).topIso.inv (((twistBundleCover n S).coord a).s i))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleCover_coord n S) i) := hh
  rw [← Scheme.homOfLE_ι _ hle, Category.assoc, hh', ← Category.assoc, comp_homOfSections]
  conv_rhs => rw [ι_eq_homOfSections n S i, comp_homOfSections]
  congr 1
  · simp only [Category.assoc]
    rw [Scheme.homOfLE_ι_assoc, twistBundleChartInv_ι_assoc, twistBundleChartInvAux,
      homOfSections_over]
  · funext a
    have e₁ : ((twistBundleCover n S).U i).topIso.inv =
        ((twistBundleCover n S).U i).ι.appLE ((twistBundleCover n S).U i) ⊤
          (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : (twistBundleChartInv n S i ≫ (twistBundleOpen n S).toScheme.homOfLE hle).appTop =
        (twistBundleChartInv n S i ≫ (twistBundleOpen n S).toScheme.homOfLE hle).appLE ⊤ ⊤
          le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hV : (twistBundleCover n S).U i ≤
        (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := le_of_eq (by simp)
    have e₃ : (twistBundleOpen n S).toScheme.presheaf.map
        (homOfLE (nonvanishing_coord _ _).le).op ((twistBundleCover₀ n S).ratio (some i) (some a)) =
        (twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i))
          ((twistBundleCover n S).U i) hV (coordRatio (Option n) S (some i) (some a)) := rfl
    dsimp only
    rw [Scheme.CoordinateCover.coord_s, twistBundleCover_ratio, e₁, e₂, e₃,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [appLE_eq_of_eq (show ((twistBundleChartInv n S i ≫
        (twistBundleOpen n S).toScheme.homOfLE hle) ≫ ((twistBundleCover n S).U i).ι) ≫
        (twistBundleOpen n S).ι = twistBundleChartInvAux n S i by
      simp only [Category.assoc, Scheme.homOfLE_ι_assoc, twistBundleChartInv_ι])]
    exact (homOfSections_appLE_coordRatio (S := S) _ (twistBundleChartInvSections n S i)
      (span_twistBundleChartInvSections n S i) (twistBundleChartInvSections_some_self n S i)
      (some a) _).trans rfl

lemma twistBundleChartInv_comp_chartHom (i : n) :
    twistBundleChartInv n S i ≫ twistBundleChartHom n S i = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, twistBundleChartHom_over, Category.id_comp,
      ← cancel_mono (standardOpen n S i).ι, Category.assoc, morphismRestrict_ι]
    exact twistBundleChartInv_comp_π n S i
  · obtain rfl : j = ⟨0⟩ := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, twistBundleChartHom,
      AffineSpace.homOfVector_appTop_coord, twistBundleChartInv_appTop_fiberCoord,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- A morphism into `ℙ(n; S)` landing in `D₊(Tᵢ)` is defined by the pulled back ratios
`Tₐ / Tᵢ`. -/
lemma eq_homOfSections_of_preimage_eq_top {X : Scheme.{u}} (f : X ⟶ ℙ(n; S)) (i : n)
    (hf : f ⁻¹ᵁ standardOpen n S i = ⊤) :
    f = homOfSections (f ≫ ℙ(n; S) ↘ S)
      (fun a ↦ f.appLE (standardOpen n S i) ⊤ hf.ge (coordRatio n S i a))
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by
        dsimp only
        rw [← standardCoordinateCover_ratio, (standardCoordinateCover n S).ratio_self, map_one]
        exact isUnit_one)) := by
  have hr : Set.range f.base ⊆ Set.range (standardOpen n S i).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : x ∈ f ⁻¹ᵁ standardOpen n S i := by rw [hf]; trivial
    exact this
  let e := IsOpenImmersion.lift _ _ hr
  have he : e ≫ (standardOpen n S i).ι = f := IsOpenImmersion.lift_fac _ _ _
  conv_lhs => rw [← he, ι_eq_homOfSections n S i, comp_homOfSections]
  congr 1
  · rw [← Category.assoc, he]
  · funext a
    have e₁ : (standardOpen n S i).topIso.inv =
        (standardOpen n S i).ι.appLE (standardOpen n S i) ⊤
          (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : e.appTop = e.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    dsimp only
    rw [e₁, e₂, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq he]

lemma twistBundleπ_appLE_coordRatio' (i k : n) (h h') :
    (twistBundleπ n S).appLE (standardOpen n S i) (twistBundleπ n S ⁻¹ᵁ standardOpen n S i) h
        (coordRatio n S i k) =
      (twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i))
        (twistBundleπ n S ⁻¹ᵁ standardOpen n S i) h'
          (coordRatio (Option n) S (some i) (some k)) := by
  have hle : twistBundleπ n S ⁻¹ᵁ standardOpen n S i ≤ (twistBundleCover n S).U i := by
    rw [twistBundleπ_preimage_standardOpen, twistBundleCover_U]
  have eL : (twistBundleCover n S).U i ≤ twistBundleπ n S ⁻¹ᵁ standardOpen n S i := by
    rw [twistBundleπ_preimage_standardOpen, twistBundleCover_U]
  have eR : (twistBundleCover n S).U i ≤
      (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := by
    rw [twistBundleCover_U]
  calc _ = ((twistBundleπ n S).appLE (standardOpen n S i) _ eL ≫
        (twistBundleOpen n S).toScheme.presheaf.map (homOfLE hle).op) (coordRatio n S i k) := by
        rw [Scheme.Hom.appLE_map]
    _ = ((twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i)) _ eR ≫
        (twistBundleOpen n S).toScheme.presheaf.map (homOfLE hle).op)
          (coordRatio (Option n) S (some i) (some k)) := by
        rw [CommRingCat.comp_apply, CommRingCat.comp_apply, twistBundleπ_appLE_coordRatio]
    _ = _ := by rw [Scheme.Hom.appLE_map]

end ProjectiveSpace

end AlgebraicGeometry
