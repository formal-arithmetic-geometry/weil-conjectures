/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.KunnethStructureSheaf.CechBijective
public import WeilConjectures.AlgebraicGeometry.AffineCoverClosedPoint
public import WeilConjectures.AlgebraicGeometry.Cohomology.KunnethStructureSheaf.Leray
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.CrossIdeal

/-!
# `H¹` of the structure sheaf of a product

Let `X`, `Y` be proper schemes over a field `K` with `H⁰(X, 𝒪_X) = H⁰(Y, 𝒪_Y) = K`, and let
`x`, `y` be `K`-points of `X`, `Y`. Restriction to the slices `X × {y}` and `{x} × Y` identifies
`H¹(X ×_K Y, 𝒪)` with `H¹(X, 𝒪_X) ⊕ H¹(Y, 𝒪_Y)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.bijective_H_one_unit_prod`

## Implementation details

The restriction of `H¹(X ×_K Y, 𝒪)` to the slice `i : X ⟶ X ×_K Y` is spelled as the map
`H¹(X ×_K Y, 𝒪) ⟶ H¹(X ×_K Y, i_* 𝒪_X)` induced by `i^♯ : 𝒪 ⟶ i_* 𝒪_X`. Its target is
`H¹(X, 𝒪_X)`, since `i` is affine
(`AlgebraicGeometry.Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))]

/-- The slice `X × {y} ⟶ X ×_K Y` at a `K`-point `y` of `Y`. -/
noncomputable def sliceLeft (y : Spec (.of K) ⟶ Y) (hy : y ≫ Y ↘ Spec (.of K) = 𝟙 _) :
    X ⟶ Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) :=
  pullback.lift (𝟙 X) (X ↘ Spec (.of K) ≫ y) (by rw [Category.assoc, hy]; simp)

/-- The slice `{x} × Y ⟶ X ×_K Y` at a `K`-point `x` of `X`. -/
noncomputable def sliceRight (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _) :
    Y ⟶ Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) :=
  pullback.lift (Y ↘ Spec (.of K) ≫ x) (𝟙 Y) (by rw [Category.assoc, hx]; simp)

/-- The slice `X × {y}` is the base change of the point `y` along the second projection. -/
lemma isPullback_sliceLeft (y : Spec (.of K) ⟶ Y) (hy : y ≫ Y ↘ Spec (.of K) = 𝟙 _) :
    IsPullback (sliceLeft (X := X) y hy) (X ↘ Spec (.of K))
      (pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))) y := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    (h₂₂ := Y ↘ Spec (.of K)) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [sliceLeft, pullback.lift_fst, hy]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The slice `{x} × Y` is the base change of the point `x` along the first projection. -/
lemma isPullback_sliceRight (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _) :
    IsPullback (sliceRight (Y := Y) x hx) (Y ↘ Spec (.of K))
      (pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))) x := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    (h₂₂ := X ↘ Spec (.of K)) ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  rw [sliceRight, pullback.lift_snd, hx]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **`H¹` of the structure sheaf of a product.** Let `X`, `Y` be proper over a field `K` with
`H⁰(X, 𝒪_X) = H⁰(Y, 𝒪_Y) = K`, and let `x`, `y` be `K`-points of `X`, `Y`. Then restriction to
the slices `X × {y}` and `{x} × Y` is a bijection
`H¹(X ×_K Y, 𝒪) → H¹(X ×_K Y, i_* 𝒪_X) × H¹(X ×_K Y, j_* 𝒪_Y)`, where `i`, `j` are the slice
inclusions. -/
theorem bijective_H_one_unit_prod [IsProper (X ↘ Spec (.of K))] [IsProper (Y ↘ Spec (.of K))]
    [GlobalSectionsBijective K X] [GlobalSectionsBijective K Y]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _)
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ Y ↘ Spec (.of K) = 𝟙 _) :
    Function.Bijective fun c : (Modules.unit
        (Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))).H 1 ↦
      (H.map (SheafOfModules.unitToPushforwardObjUnit (sliceLeft y hy).toRingCatSheafHom) 1 c,
        H.map (SheafOfModules.unitToPushforwardObjUnit (sliceRight x hx).toRingCatSheafHom)
          1 c) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K))
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of K))]
    infer_instance
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from (Y ↘ Spec (.of K))]
    infer_instance
  have : IsSeparated (terminal.from (Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))) := by
    rw [← terminal.comp_from (pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) ≫
      X ↘ Spec (.of K))]
    infer_instance
  have : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id (X ↘ Spec (.of K)) x hx
  have : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id (Y ↘ Spec (.of K)) y hy
  have hx₀ : IsClosed {x default} := by
    rw [← Set.range_unique]
    exact x.isClosedEmbedding.isClosed_range
  have hy₀ : IsClosed {y default} := by
    rw [← Set.range_unique]
    exact y.isClosedEmbedding.isClosed_range
  obtain ⟨α, _, Ux, a₀, hUx, hUcov, ha₀⟩ := exists_finite_affine_cover_unique_mem X hx₀
  obtain ⟨β, _, Vy, b₀, hVy, hVcov, hb₀⟩ := exists_finite_affine_cover_unique_mem Y hy₀
  let W : α × β → (Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))).Opens :=
    fun p ↦ IdealSheafData.Kunneth.prodOpen K X Y (Ux p.1) (Vy p.2)
  have hW (s : Finset (α × β)) (hs : s.Nonempty) : IsAffineOpen (⨅ p ∈ s, W p) :=
    IsAffineOpen.biInf _ s.finite_toSet hs fun p _ ↦
      isAffineOpen_preimage_inf_preimage_pullback _ _ (hUx p.1) (hVy p.2)
  have hWcov : iSup W = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1
      (hUcov.ge (Set.mem_univ (pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) z)))
    obtain ⟨b, hb⟩ := Opens.mem_iSup.1
      (hVcov.ge (Set.mem_univ (pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) z)))
    exact Opens.mem_iSup.2 ⟨(a, b), ha, hb⟩
  have hi := isPullback_sliceLeft (X := X) y hy
  have hj := isPullback_sliceRight (Y := Y) x hx
  have : IsClosedImmersion (sliceLeft (X := X) y hy) :=
    MorphismProperty.of_isPullback hi.flip inferInstance
  have : IsClosedImmersion (sliceRight (Y := Y) x hx) :=
    MorphismProperty.of_isPullback hj.flip inferInstance
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit
    (R := (Limits.pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))).ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent ((SheafOfModules.pushforward
      (sliceLeft (X := X) y hy).toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isAffineHom (sliceLeft (X := X) y hy)
    (SheafOfModules.unit X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent ((SheafOfModules.pushforward
      (sliceRight (Y := Y) x hx).toRingCatSheafHom).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isAffineHom (sliceRight (Y := Y) x hx)
    (SheafOfModules.unit Y.ringCatSheaf)
  refine bijective_H_map_prod_of_bijective_cechCohomologyFunctor_map W hW hWcov _ _ 1 ?_
  exact bijective_homologyMap_cechComplex_slices Ux Vy hUx hVy
    (fun a a' ↦ (hUx a).inf (hUx a')) (fun b b' ↦ (hVy b).inf (hVy b')) hUcov hVcov
    (fun k q ↦ isAffineOpen_iInf_fin hW k q) x y
    (fun _ hs ↦ TheoremOfCube.eq_zero_of_mem_idealOfOpens_ker x hx hs)
    (fun _ hs ↦ TheoremOfCube.eq_zero_of_mem_idealOfOpens_ker y hy hs) a₀ b₀ ha₀ hb₀ _ _ hi hj
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme.Modules
