/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Hyperplane
public import WeilConjectures.AlgebraicGeometry.VectorBundle
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The total space of `𝒪(1)` on projective space

The total space of the line bundle `𝒪(1)` on `ℙ(n; S)` is the open subscheme
`W = ⋃ᵢ D₊(Tᵢ)` of `ℙ(Option n; S)`, the complement of the point `[0 : ⋯ : 0 : 1]`, with the
projection `[x : t] ↦ [x]` (`AlgebraicGeometry.ProjectiveSpace.twistBundleπ`); its zero section is
the hyperplane embedding.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover.restrictOpen`: the restriction of a coordinate cover to
  an open subscheme.
- `AlgebraicGeometry.ProjectiveSpace.twistBundleOpen`: the open `W`.
- `AlgebraicGeometry.ProjectiveSpace.twistBundleπ`: the projection `W ⟶ ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.twistBundleChart`: the charts `π⁻¹(D₊(Tᵢ)) ≅ 𝔸¹_{D₊(Tᵢ)}`.
- `AlgebraicGeometry.ProjectiveSpace.twistBundle`: `𝒪(1)` as a `VectorBundle 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι) (W : X.Opens)

/-- The restriction of a coordinate cover of `X` to an open subscheme `W`. -/
noncomputable def restrictOpen : W.toScheme.CoordinateCover ι where
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
lemma restrictOpen_U (i : ι) : (𝒟.restrictOpen W).U i = W.ι ⁻¹ᵁ 𝒟.U i := rfl

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
  (standardCoordinateCover (Option n) S).restrictOpen (twistBundleOpen n S)

lemma iSup_nonvanishing_twistBundleCover₀ :
    ⨆ i : n, ((twistBundleCover₀ n S).coord (some i)).nonvanishing = ⊤ := by
  simp only [nonvanishing_coord, twistBundleCover₀, Scheme.CoordinateCover.restrictOpen_U,
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

lemma twistBundleChartHom_comp_chartInv (i : n) :
    twistBundleChartHom n S i ≫ twistBundleChartInv n S i = 𝟙 _ := by
  have hf : ((twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ (twistBundleOpen n S).ι) ⁻¹ᵁ
      standardOpen (Option n) S (some i) = ⊤ := by
    change (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ⁻¹ᵁ
      ((twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i)) = ⊤
    rw [← twistBundleπ_preimage_standardOpen]
    exact Scheme.Opens.ι_preimage_self _
  have e₁ : (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).topIso.inv =
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι.appLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i)
        ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  rw [← cancel_mono ((twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ (twistBundleOpen n S).ι),
    Category.assoc, twistBundleChartInv_ι, Category.id_comp, twistBundleChartInvAux,
    comp_homOfSections]
  conv_rhs => rw [eq_homOfSections_of_preimage_eq_top (Option n) S _ (some i) hf]
  congr 1
  · rw [twistBundleChartHom_over_assoc, morphismRestrict_ι_assoc, twistBundleπ_over]
    simp only [Category.assoc]
  · funext a
    cases a with
    | none =>
      change (twistBundleChartHom n S i).appTop (AffineSpace.coord _ ⟨0⟩) = _
      rw [twistBundleChartHom, AffineSpace.homOfVector_appTop_coord, twistBundleFiberCoord, e₁,
        ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    | some k =>
      have e₀ : (standardOpen n S i).topIso.inv =
          (standardOpen n S i).ι.appLE (standardOpen n S i) ⊤
            (Scheme.Opens.ι_preimage_self _).ge := by
        rw [Scheme.Opens.ι_appLE]
        rfl
      have e₂ : (twistBundleπ n S ∣_ standardOpen n S i).appTop =
          (twistBundleπ n S ∣_ standardOpen n S i).appLE ⊤ ⊤ le_top := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        rfl
      change (twistBundleChartHom n S i).appTop ((𝔸(ULift.{u} (Fin 1);
        (standardOpen n S i).toScheme) ↘ _).appTop _) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, twistBundleChartHom_over, e₀, e₂,
        ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
        appLE_eq_of_eq (morphismRestrict_ι _ _),
        ← Scheme.Hom.appLE_comp_appLE _ _ _ (twistBundleπ n S ⁻¹ᵁ standardOpen n S i) _ le_rfl
          (Scheme.Opens.ι_preimage_self _).ge,
        CommRingCat.comp_apply, twistBundleπ_appLE_coordRatio' n S i k _ (by
          rw [← twistBundleπ_preimage_standardOpen]),
        ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- The chart `π⁻¹(D₊(Tᵢ)) ≅ 𝔸¹_{D₊(Tᵢ)}` of the total space of `𝒪(1)`. -/
noncomputable def twistBundleChart (i : n) :
    (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).toScheme ≅
      𝔸(ULift.{u} (Fin 1); (standardOpen n S i).toScheme) where
  hom := twistBundleChartHom n S i
  inv := twistBundleChartInv n S i
  hom_inv_id := twistBundleChartHom_comp_chartInv n S i
  inv_hom_id := twistBundleChartInv_comp_chartHom n S i

/-- The chart carries the zero section to the zero section. -/
lemma twistBundleZero_resLE_chart (i : n) :
    (twistBundleZero n S).resLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i) (standardOpen n S i)
        (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (twistBundleZero_comp_π n S) _) ≫
      (twistBundleChart n S i).hom = AffineSpace.zeroSection _ _ := by
  refine AffineSpace.hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, twistBundleChart, twistBundleChartHom_over,
      AffineSpace.zeroSection_over, ← cancel_mono (standardOpen n S i).ι, Category.assoc,
      morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, twistBundleZero_comp_π,
      Category.comp_id, Category.id_comp]
  · obtain rfl : j = ⟨0⟩ := Subsingleton.elim _ _
    rw [AffineSpace.zeroSection_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      twistBundleChart]
    dsimp only
    rw [twistBundleChartHom, AffineSpace.homOfVector_appTop_coord, twistBundleFiberCoord]
    have e₁ : (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).topIso.inv =
        (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι.appLE
          (twistBundleπ n S ⁻¹ᵁ standardOpen n S i) ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : ((twistBundleZero n S).resLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i)
        (standardOpen n S i)
          (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (twistBundleZero_comp_π n S) _)).appTop =
        ((twistBundleZero n S).resLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i)
          (standardOpen n S i)
            (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (twistBundleZero_comp_π n S) _)).appLE
              ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hh := Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover n S)
      (hyperplaneSections n S) (span_hyperplaneSections n S) (ℙ(n; S) ↘ S) i
    have hh' : (standardOpen n S i).ι ≫ hyperplane n S = homOfSections
        ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
        (fun a ↦ (standardOpen n S i).topIso.inv ((hyperplaneSections n S a).s i))
        (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections n S) i) := hh
    rw [e₁, e₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq (show ((twistBundleZero n S).resLE _ _ _ ≫
        (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι) ≫ (twistBundleOpen n S).ι =
          (standardOpen n S i).ι ≫ hyperplane n S by
        rw [Scheme.Hom.resLE_comp_ι, Category.assoc, twistBundleZero_ι]),
      appLE_eq_of_eq hh']
    refine (homOfSections_appLE_coordRatio (S := S) ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun a ↦ (standardOpen n S i).topIso.inv ((hyperplaneSections n S a).s i))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections n S) i)
      (hyperplaneSections_some_s_self n S i) none _).trans ?_
    simp [hyperplaneSections, Scheme.CoordinateCover.zeroSection]

lemma twistBundleπ_appLE_coordRatio_of_le (i k : n) {V : (twistBundleOpen n S).toScheme.Opens}
    (hV : V ≤ (twistBundleCover n S).U i) (h h') :
    (twistBundleπ n S).appLE (standardOpen n S i) V h (coordRatio n S i k) =
      (twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i)) V h'
        (coordRatio (Option n) S (some i) (some k)) := by
  have eL : (twistBundleCover n S).U i ≤ twistBundleπ n S ⁻¹ᵁ standardOpen n S i := by
    rw [twistBundleπ_preimage_standardOpen, twistBundleCover_U]
  have eR : (twistBundleCover n S).U i ≤
      (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := by
    rw [twistBundleCover_U]
  calc _ = ((twistBundleπ n S).appLE (standardOpen n S i) _ eL ≫
        (twistBundleOpen n S).toScheme.presheaf.map (homOfLE hV).op) (coordRatio n S i k) := by
        rw [Scheme.Hom.appLE_map]
    _ = ((twistBundleOpen n S).ι.appLE (standardOpen (Option n) S (some i)) _ eR ≫
        (twistBundleOpen n S).toScheme.presheaf.map (homOfLE hV).op)
          (coordRatio (Option n) S (some i) (some k)) := by
        rw [CommRingCat.comp_apply, CommRingCat.comp_apply, twistBundleπ_appLE_coordRatio]
    _ = _ := by rw [Scheme.Hom.appLE_map]

/-- The restriction of a function on an open `U` of the base to its preimage. -/
lemma morphismRestrict_appTop_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv x) =
      (f ⁻¹ᵁ U).topIso.inv (f.appLE U (f ⁻¹ᵁ U) le_rfl x) := by
  have e₀ : U.topIso.inv = U.ι.appLE U ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have e₁ : (f ⁻¹ᵁ U).topIso.inv =
      (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ U) ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have e₂ : (f ∣_ U).appTop = (f ∣_ U).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e₀, e₁, e₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq (morphismRestrict_ι f U)]

/-- The transition functions of the total space of `𝒪(1)` are linear: on `π⁻¹(D₊(Tᵢ) ∩ D₊(Tⱼ))`
the fibre coordinates satisfy `T_∗ / Tⱼ = (Tᵢ / Tⱼ) (T_∗ / Tᵢ)`. -/
lemma twistBundle_linear (i j : n) :
    ∃ M : Matrix (Fin 1) (Fin 1) Γ((standardOpen n S i ⊓ standardOpen n S j).toScheme, ⊤),
      IsUnit M.det ∧ ∀ a,
        ((twistBundleOpen n S).toScheme.homOfLE ((twistBundleπ n S).preimage_mono inf_le_right) ≫
          (twistBundleChart n S j).hom).appTop (AffineSpace.coord _ (ULift.up a)) =
        ∑ b, (twistBundleπ n S ∣_ (standardOpen n S i ⊓ standardOpen n S j)).appTop (M a b) *
          ((twistBundleOpen n S).toScheme.homOfLE ((twistBundleπ n S).preimage_mono inf_le_left) ≫
            (twistBundleChart n S i).hom).appTop (AffineSpace.coord _ (ULift.up b)) := by
  have hU : standardOpen n S i ⊓ standardOpen n S j ≤
      ℙ(n; S).basicOpen (coordRatio n S j i) := by
    rw [← standardCoordinateCover_ratio, (standardCoordinateCover n S).basicOpen_ratio,
      standardCoordinateCover_U, standardCoordinateCover_U, inf_comm]
  refine ⟨Matrix.of fun _ _ ↦ (standardOpen n S i ⊓ standardOpen n S j).topIso.inv
    (ℙ(n; S).presheaf.map (homOfLE inf_le_right).op (coordRatio n S j i)), ?_, fun a ↦ ?_⟩
  · rw [Matrix.det_unique, Matrix.of_apply]
    exact (Scheme.isUnit_map_of_le_basicOpen (coordRatio n S j i) hU).map _
  obtain rfl : a = 0 := Subsingleton.elim _ _
  rw [Fin.sum_univ_one, Matrix.of_apply, morphismRestrict_appTop_topIso_inv]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, twistBundleChart,
    twistBundleChartHom, AffineSpace.homOfVector_appTop_coord, twistBundleFiberCoord,
    Scheme.homOfLE_appTop_topIso_inv]
  rw [← map_mul]
  congr 1
  have hZi : twistBundleπ n S ⁻¹ᵁ (standardOpen n S i ⊓ standardOpen n S j) ≤
      (twistBundleCover n S).U j := by
    rw [twistBundleCover_U, ← twistBundleπ_preimage_standardOpen]
    exact (twistBundleπ n S).preimage_mono inf_le_right
  have hO : twistBundleπ n S ⁻¹ᵁ (standardOpen n S i ⊓ standardOpen n S j) ≤
      (twistBundleOpen n S).ι ⁻¹ᵁ (standardOpen (Option n) S (some i) ⊓
        standardOpen (Option n) S (some j)) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ← twistBundleπ_preimage_standardOpen,
      ← twistBundleπ_preimage_standardOpen]
  simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [twistBundleπ_appLE_coordRatio_of_le n S j i hZi _ (hO.trans
      ((twistBundleOpen n S).ι.preimage_mono inf_le_right))]
  rw [← Scheme.Hom.map_appLE (twistBundleOpen n S).ι hO (homOfLE (inf_le_right :
      standardOpen (Option n) S (some i) ⊓ standardOpen (Option n) S (some j) ≤ _)).op,
    ← Scheme.Hom.map_appLE (twistBundleOpen n S).ι hO (homOfLE (inf_le_left :
      standardOpen (Option n) S (some i) ⊓ standardOpen (Option n) S (some j) ≤ _)).op]
  simp only [CommRingCat.comp_apply]
  rw [← map_mul]
  congr 1
  rw [map_coordRatio_eq_mul (inf_le_right : standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j) ≤ _) inf_le_left none, mul_comm]

/-- **The line bundle `𝒪(1)` on `ℙ(n; S)`** as a vector bundle of rank one: the total space
`W = ⋃ᵢ D₊(Tᵢ) ⊆ ℙ(Option n; S)` with the projection `[x : t] ↦ [x]`, the zero section the
hyperplane embedding, the charts `π⁻¹(D₊(Tᵢ)) ≅ 𝔸¹_{D₊(Tᵢ)}` given by the fibre coordinate
`T_∗ / Tᵢ`, and the transition functions `Tᵢ / Tⱼ`. -/
noncomputable def twistBundle : VectorBundle 1 (twistBundleπ n S) where
  zero := twistBundleZero n S
  zero_comp := twistBundleZero_comp_π n S
  ι := n
  U := standardOpen n S
  iSup_U := iSup_standardOpen n S
  chart := twistBundleChart n S
  chart_over := twistBundleChartHom_over n S
  zero_chart := twistBundleZero_resLE_chart n S
  linear := twistBundle_linear n S

/-- The coordinate of the chart of `𝒪(1)` over `D₊(Tᵢ)` is the fibre coordinate `T_∗ / Tᵢ`. -/
lemma twistBundle_coord (i : n) (a : Fin 1) :
    (twistBundle n S).coord i a = twistBundleFiberCoord n S i :=
  AffineSpace.homOfVector_appTop_coord _ _ _

@[simp]
lemma twistBundle_zero : (twistBundle n S).zero = twistBundleZero n S := rfl

/-! ### The coordinate sections of `𝒪(1)` -/

/-- The sections defining the coordinate section `[x] ↦ [x : x_t]`: the coordinates `Tᵢ`, and
`T_t` for the extra coordinate. -/
noncomputable def twistBundleSectionSections (t : n) :
    Option n → (standardCoordinateCover n S).Section 1
  | none => (standardCoordinateCover n S).coord t
  | some i => (standardCoordinateCover n S).coord i

lemma span_twistBundleSectionSections (t : n) (i : n) :
    Ideal.span (Set.range fun a ↦ (twistBundleSectionSections n S t a).s i) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨some i, rfl⟩) ?_
  simp [twistBundleSectionSections, (standardCoordinateCover n S).ratio_self i]

lemma twistBundleSectionSections_some_s_self (t : n) (i : n) :
    (standardOpen n S i).topIso.inv ((twistBundleSectionSections n S t (some i)).s i) = 1 := by
  simp [twistBundleSectionSections, (standardCoordinateCover n S).ratio_self i]

/-- The coordinate section `[x] ↦ [x : x_t]` as a morphism `ℙ(n; S) ⟶ ℙ(Option n; S)`. -/
noncomputable def twistBundleSectionAux (t : n) : ℙ(n; S) ⟶ ℙ(Option n; S) :=
  Scheme.CoordinateCover.hom (twistBundleSectionSections n S t)
    (span_twistBundleSectionSections n S t) (ℙ(n; S) ↘ S)

@[reassoc (attr := simp)]
lemma twistBundleSectionAux_over (t : n) :
    twistBundleSectionAux n S t ≫ ℙ(Option n; S) ↘ S = ℙ(n; S) ↘ S :=
  Scheme.CoordinateCover.hom_over _ _ _

lemma twistBundleSectionAux_preimage_standardOpen_some (t : n) (i : n) :
    twistBundleSectionAux n S t ⁻¹ᵁ standardOpen (Option n) S (some i) = standardOpen n S i := by
  rw [twistBundleSectionAux, Scheme.CoordinateCover.preimage_hom_standardOpen]
  exact nonvanishing_coord _ i

lemma range_twistBundleSectionAux_subset (t : n) :
    Set.range (twistBundleSectionAux n S t).base ⊆ Set.range (twistBundleOpen n S).ι.base := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen n S).ge (Set.mem_univ x))
  rw [Scheme.Opens.range_ι]
  have hx : x ∈ twistBundleSectionAux n S t ⁻¹ᵁ standardOpen (Option n) S (some i) := by
    rw [twistBundleSectionAux_preimage_standardOpen_some]
    exact hi
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩

/-- The section `[x] ↦ [x : x_t]` of `𝒪(1)`, the coordinate `T_t`, as a morphism `ℙ(n; S) ⟶ W`. -/
noncomputable def twistBundleSection (t : n) : ℙ(n; S) ⟶ (twistBundleOpen n S).toScheme :=
  IsOpenImmersion.lift (twistBundleOpen n S).ι (twistBundleSectionAux n S t)
    (range_twistBundleSectionAux_subset n S t)

@[reassoc (attr := simp)]
lemma twistBundleSection_ι (t : n) :
    twistBundleSection n S t ≫ (twistBundleOpen n S).ι = twistBundleSectionAux n S t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The coordinate section is a section of the projection.
On the chart `D₊(Tᵢ)` of `ℙ(n; S)` both sides are `homOfSections` of the ratios
`Tⱼ / Tᵢ` (`AlgebraicGeometry.ProjectiveSpace.comp_homOfSections`,
`Scheme.CoordinateCover.ι_hom`): the ratios of `twistBundleCover` are the restrictions of
`T_{some j} / T_{some i}`, which the hyperplane embedding pulls back to `Tⱼ / Tᵢ`. -/
lemma twistBundleSection_comp_π (t : n) :
    twistBundleSection n S t ≫ twistBundleπ n S = 𝟙 ℙ(n; S) := by
  refine Scheme.Opens.hom_ext_of_iSup_eq_top (fun i ↦ standardOpen n S i) (iSup_standardOpen n S)
    _ _ fun i ↦ ?_
  have hr : Set.range ((standardOpen n S i).ι ≫ twistBundleSection n S t).base ⊆
      Set.range ((twistBundleCover n S).U i).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, twistBundleCover_U]
    have hx : x.1 ∈ twistBundleSectionAux n S t ⁻¹ᵁ standardOpen (Option n) S (some i) := by
      rw [twistBundleSectionAux_preimage_standardOpen_some]
      exact x.2
    change ((standardOpen n S i).ι ≫ twistBundleSection n S t ≫ (twistBundleOpen n S).ι).base x ∈
      standardOpen (Option n) S (some i)
    rw [twistBundleSection_ι]
    exact hx
  let c := IsOpenImmersion.lift _ _ hr
  have hc : c ≫ ((twistBundleCover n S).U i).ι =
      (standardOpen n S i).ι ≫ twistBundleSection n S t :=
    IsOpenImmersion.lift_fac _ _ _
  have hh := Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover n S)
    (twistBundleSectionSections n S t) (span_twistBundleSectionSections n S t) (ℙ(n; S) ↘ S) i
  rw [Scheme.CoordinateCover.localHom] at hh
  rw [← Category.assoc, ← hc, Category.assoc, twistBundleπ, Scheme.CoordinateCover.ι_hom,
    Scheme.CoordinateCover.localHom, comp_homOfSections, Category.comp_id]
  conv_rhs => rw [ι_eq_homOfSections n S i]
  congr 1
  · rw [← Category.assoc c, hc, Category.assoc, twistBundleSection_ι_assoc,
      twistBundleSectionAux_over]
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
      (standardOpen n S i).ι ≫ twistBundleSectionAux n S t by
        rw [hc, Category.assoc, twistBundleSection_ι])]
    have hh' : (standardOpen n S i).ι ≫ twistBundleSectionAux n S t = homOfSections
        ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
        (fun a ↦ (standardOpen n S i).topIso.inv ((twistBundleSectionSections n S t a).s i))
        (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleSectionSections n S t) i) := hh
    rw [appLE_eq_of_eq hh']
    exact (homOfSections_appLE_coordRatio (S := S) ((standardOpen n S i).ι ≫ ℙ(n; S) ↘ S)
      (fun a ↦ (standardOpen n S i).topIso.inv ((twistBundleSectionSections n S t a).s i))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_twistBundleSectionSections n S t) i)
      (twistBundleSectionSections_some_s_self n S t i) (some a) _).trans rfl


/-- On the hyperplane `ℙ(m; S) ⊆ ℙ(Option m; S)`, the coordinate section `[x] ↦ [x : x_∗]` agrees
with the zero section: both are `[x : 0] ↦ [x : 0 : 0]`. -/
lemma hyperplane_comp_twistBundleSectionAux_none {m : Type u} :
    hyperplane m S ≫ twistBundleSectionAux (Option m) S none =
      hyperplane m S ≫ hyperplane (Option m) S := by
  refine Scheme.Opens.hom_ext_of_iSup_eq_top (fun k ↦ standardOpen m S k) (iSup_standardOpen m S)
    _ _ fun k ↦ ?_
  have hr : Set.range ((standardOpen m S k).ι ≫ hyperplane m S).base ⊆
      Set.range (standardOpen (Option m) S (some k)).ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x.1 ∈ hyperplane m S ⁻¹ᵁ standardOpen (Option m) S (some k) := by
      rw [hyperplane_preimage_standardOpen_some]
      exact x.2
    exact hx
  let c := IsOpenImmersion.lift _ _ hr
  have hc : c ≫ (standardOpen (Option m) S (some k)).ι = (standardOpen m S k).ι ≫ hyperplane m S :=
    IsOpenImmersion.lift_fac _ _ _
  have h₁ : (standardOpen (Option m) S (some k)).ι ≫ twistBundleSectionAux (Option m) S none =
      homOfSections ((standardOpen (Option m) S (some k)).ι ≫ ℙ(Option m; S) ↘ S)
        (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
          ((twistBundleSectionSections (Option m) S none a).s (some k)))
        (Scheme.CoordinateCover.span_topIso_inv _
          (span_twistBundleSectionSections (Option m) S none) (some k)) :=
    Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover (Option m) S) _ _ _ _
  have h₂ : (standardOpen (Option m) S (some k)).ι ≫ hyperplane (Option m) S =
      homOfSections ((standardOpen (Option m) S (some k)).ι ≫ ℙ(Option m; S) ↘ S)
        (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
          ((hyperplaneSections (Option m) S a).s (some k)))
        (Scheme.CoordinateCover.span_topIso_inv _
          (span_hyperplaneSections (Option m) S) (some k)) :=
    Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover (Option m) S) _ _ _ _
  rw [← Category.assoc, ← hc, Category.assoc, h₁, ← Category.assoc, ← hc, Category.assoc, h₂,
    comp_homOfSections, comp_homOfSections]
  congr 1
  funext b
  cases b with
  | some a => rfl
  | none =>
    simp only [twistBundleSectionSections, hyperplaneSections,
      Scheme.CoordinateCover.zeroSection, map_zero]
    rw [Scheme.CoordinateCover.coord_s, standardCoordinateCover_ratio]
    have e₀ : (standardOpen (Option m) S (some k)).topIso.inv =
        (standardOpen (Option m) S (some k)).ι.appLE (standardOpen (Option m) S (some k)) ⊤
          (Scheme.Opens.ι_preimage_self _).ge := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    have e₂ : c.appTop = c.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hh' : (standardOpen m S k).ι ≫ hyperplane m S = homOfSections
        ((standardOpen m S k).ι ≫ ℙ(m; S) ↘ S)
        (fun a ↦ (standardOpen m S k).topIso.inv ((hyperplaneSections m S a).s k))
        (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections m S) k) :=
      Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover m S) _ _ _ _
    rw [e₀, e₂, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hc,
      appLE_eq_of_eq hh']
    refine (homOfSections_appLE_coordRatio (S := S) ((standardOpen m S k).ι ≫ ℙ(m; S) ↘ S)
      (fun a ↦ (standardOpen m S k).topIso.inv ((hyperplaneSections m S a).s k))
      (Scheme.CoordinateCover.span_topIso_inv _ (span_hyperplaneSections m S) k)
      (hyperplaneSections_some_s_self m S k) none _).trans ?_
    simp [hyperplaneSections, Scheme.CoordinateCover.zeroSection]


end ProjectiveSpace

end AlgebraicGeometry
