/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.CounitIso
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!

# The exceptional Künneth formula for a closed immersion

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, `Y₁`, `Y₂` separated
of finite type over `k` and `i : Z ⟶ Y₁` a closed immersion, with base change
`ι = i × 𝟙 : Z ×_k Y₂ ⟶ Y₁ ×_k Y₂`. For `N₁ ∈ Dctf(Y₁, Λ)` and `N₂ ∈ Dctf(Y₂, Λ)`,

`Rι^! (N₁ ⊠ N₂) ≅ Ri^! N₁ ⊠ N₂`.

This is the closed-immersion case of the exceptional Künneth map `α` of
`prop-trf-exceptional-kunneth`, handled, as in the blueprint, by the supported localization
triangle `Ri_* Ri^! N₁ ⟶ N₁ ⟶ Rj_* Lj^* N₁ ⟶` (`sk-prop-sf-localization`) and the ordinary
Künneth formula with an identity factor (`sk-lem-sf-kunneth-star`) for the closed immersion `i`
and the complementary open immersion `j`: the external product with `N₂` of the localization
triangle of `N₁` is a distinguished triangle `Rι_*(Ri^! N₁ ⊠ N₂) ⟶ N₁ ⊠ N₂ ⟶ Rj'_*(…) ⟶`, so
its first map is the counit of `Rι_! ⊣ Rι^!` at `N₁ ⊠ N₂`
(`CategoryTheory.Pretriangulated.exists_iso_counit_of_subsingleton`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_pullbackMapLeft_externalProduct`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unit `Λ_X` of `D(X_ét, Λ)` lies in `Dctf(X, Λ)`: it is the constant sheaf, which is
constructible and flat, placed in degree `0`. -/
theorem constructibleFiniteTor_tensorUnit (X : Scheme.{u}) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  (constructibleFiniteTor _ X).prop_of_iso (singleFunctorObjUnitIso _ X)
    ⟨boundedConstructible_singleFunctor_obj _ 0, 0, 0,
      torAmplitudeIn_singleFunctor_obj_of_flat Λ _ (ObjectProperty.flat_of_tensorIso (λ_ _))⟩

/-- The base change `i × 𝟙 : Z ×_S Y₂ ⟶ Y₁ ×_S Y₂` of a closed immersion is a closed
immersion. -/
instance isClosedImmersion_pullbackMapLeft {S Y₁ Y₂ Z : Scheme.{u}} (b₁ : Y₁ ⟶ S)
    (b₂ : Y₂ ⟶ S) (i : Z ⟶ Y₁) [IsClosedImmersion i] :
    IsClosedImmersion (pullbackMapLeft b₁ b₂ i) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_pullbackMapLeft b₁ b₂ i)
    inferInstance

/-- The base change `j × 𝟙 : U ×_S Y₂ ⟶ Y₁ ×_S Y₂` of an open immersion is an open
immersion. -/
instance isOpenImmersion_pullbackMapLeft {S Y₁ Y₂ U : Scheme.{u}} (b₁ : Y₁ ⟶ S)
    (b₂ : Y₂ ⟶ S) (j : U ⟶ Y₁) [IsOpenImmersion j] :
    IsOpenImmersion (pullbackMapLeft b₁ b₂ j) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_pullbackMapLeft b₁ b₂ j)
    inferInstance

/-- The base change `𝟙 × j : Y₁ ×_S U ⟶ Y₁ ×_S Y₂` of a closed immersion is a closed
immersion. -/
instance isClosedImmersion_pullbackMapRight {S Y₁ Y₂ Z : Scheme.{u}} (b₁ : Y₁ ⟶ S)
    (b₂ : Y₂ ⟶ S) (i : Z ⟶ Y₂) [IsClosedImmersion i] :
    IsClosedImmersion (pullbackMapRight b₁ b₂ i) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_pullbackMapRight b₁ b₂ i)
    inferInstance

/-- The base change `𝟙 × j : Y₁ ×_S U ⟶ Y₁ ×_S Y₂` of an open immersion is an open
immersion. -/
instance isOpenImmersion_pullbackMapRight {S Y₁ Y₂ U : Scheme.{u}} (b₁ : Y₁ ⟶ S)
    (b₂ : Y₂ ⟶ S) (j : U ⟶ Y₂) [IsOpenImmersion j] :
    IsOpenImmersion (pullbackMapRight b₁ b₂ j) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_pullbackMapRight b₁ b₂ j)
    inferInstance

/-- The base changes `i × 𝟙` and `j × 𝟙` of complementary immersions `i` and `j` have disjoint
ranges. -/
lemma disjoint_range_pullbackMapLeft {S Y₁ Y₂ Z U : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
    (i : Z ⟶ Y₁) (j : U ⟶ Y₁) (hij : Disjoint (Set.range i.base) (Set.range j.base)) :
    Disjoint (Set.range (pullbackMapLeft b₁ b₂ i).base)
      (Set.range (pullbackMapLeft b₁ b₂ j).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨c, hc⟩
  have h₁ : (pullback.fst b₁ b₂).base ((pullbackMapLeft b₁ b₂ i).base a) =
      i.base ((pullback.fst (i ≫ b₁) b₂).base a) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      (isPullback_pullbackMapLeft b₁ b₂ i).w]
  have h₂ : (pullback.fst b₁ b₂).base ((pullbackMapLeft b₁ b₂ j).base c) =
      j.base ((pullback.fst (j ≫ b₁) b₂).base c) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      (isPullback_pullbackMapLeft b₁ b₂ j).w]
  rw [hc] at h₂
  exact Set.disjoint_left.1 hij ⟨_, h₁.symm⟩ ⟨_, h₂.symm⟩

/-- Blueprint `prop-trf-exceptional-kunneth`: Exceptional Künneth; the `α` map, for a closed
immersion in the first factor and the identity in the second.

For `Y₁`, `Y₂` separated of finite type over a field `k`, a closed immersion `i : Z ⟶ Y₁` with
base change `ι = i × 𝟙 : Z ×_k Y₂ ⟶ Y₁ ×_k Y₂`, `N₁ ∈ Dctf(Y₁, Λ)` and `N₂ ∈ Dctf(Y₂, Λ)`,

`Rι^! (N₁ ⊠ N₂) ≅ Ri^! N₁ ⊠ N₂`.

The external product with `N₂` of the supported localization triangle
`Ri_* Ri^! N₁ ⟶ N₁ ⟶ Rj_* Lj^* N₁ ⟶` of the complementary open immersion `j` is distinguished;
by the ordinary Künneth formula with an identity factor its vertices are
`Rι_* (Ri^! N₁ ⊠ N₂)` (`i` is proper) and `Rj'_* (Lj^* N₁ ⊠ N₂)` for `j' = j × 𝟙`
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`). The ranges of `ι`
and `j'` are disjoint, so the third vertex is right orthogonal to the essential image of `Rι_*`,
and the first map is the counit of `Rι_! ⊣ Rι^!` at `N₁ ⊠ N₂`
(`CategoryTheory.Pretriangulated.exists_iso_counit_of_subsingleton`); `Rι_*` is fully faithful
(`sk-prop-sf-closed-unit`). -/
theorem nonempty_iso_rightDerivedUpperShriek_pullbackMapLeft_externalProduct
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Y₁ Y₂ Z : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (i : Z ⟶ Y₁) [IsClosedImmersion i]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁)
    (h₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂) :
    Nonempty ((R(pullbackMapLeft b₁ b₂ i)^![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂) ≅
      externalProduct (ModuleCat.{u + 1} Λ) (i ≫ b₁) b₂ ((R(i)^![ModuleCat.{u + 1} Λ]).obj N₁)
        N₂) := by
  have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace b₁
  have : IsNoetherian Y₁ := { __ := LocallyOfFiniteType.isLocallyNoetherian b₁ }
  set ι := pullbackMapLeft b₁ b₂ i
  obtain ⟨U, hiU, -⟩ := exists_openImmersion_range_compl i
  set j := U.ι
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  set ιj := pullbackMapLeft b₁ b₂ j
  have hdisj : Disjoint (Set.range ι.base) (Set.range ιj.base) :=
    disjoint_range_pullbackMapLeft b₁ b₂ i j (by rw [hiU]; exact disjoint_compl_left)
  -- the external product with `N₂`, as a triangulated functor of the first variable
  let F := L((pullback.fst b₁ b₂)^*[ModuleCat.{u + 1} Λ]) ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) (pullback b₁ b₂)).flip.obj
      ((L((pullback.snd b₁ b₂)^*[ModuleCat.{u + 1} Λ])).obj N₂)
  have hT := supportedLocalizationTriangle_mem_distTriang (ModuleCat.{u + 1} Λ) i j hiU N₁
  have hFT := F.map_distinguished _ hT
  set A := (R(i)^![ModuleCat.{u + 1} Λ]).obj N₁
  -- the first vertex is `Rι_* (Ri^! N₁ ⊠ N₂)`
  obtain ⟨e₁⟩ := nonempty_iso_externalProduct_rightDerivedLowerStar_of_isProper Λ b₁ b₂ i A N₂
  let E₁ : (R(ι)_![ModuleCat.{u + 1} Λ]).obj (externalProduct _ (i ≫ b₁) b₂ A N₂) ≅
      (F.mapTriangle.obj (supportedLocalizationTriangle _ i j N₁
        (supportedLocalizationBoundary _ i j hiU N₁))).obj₁ :=
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ ι).app _ ≪≫ e₁.symm ≪≫
      F.mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app A).symm
  -- the third vertex is `Rj'_* (Lj^* N₁ ⊠ N₂)`
  have hj₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) U
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N₁) :=
    constructibleFiniteTor_leftDerivedUpperStar _ j h₁
  obtain ⟨e₃⟩ := nonempty_iso_externalProduct_rightDerivedLowerStar Λ b₁ b₂ j hj₁ h₂
  have h₃ : ∀ (M : _root_.DerivedCategory (Sheaf (pullback (i ≫ b₁) b₂).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) (n : ℤ), Subsingleton (((R(ι)_![ModuleCat.{u + 1} Λ]).obj M)⟦n⟧ ⟶
        (F.mapTriangle.obj (supportedLocalizationTriangle _ i j N₁
          (supportedLocalizationBoundary _ i j hiU N₁))).obj₃) := fun M n ↦
    have := subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar
      (ModuleCat.{u + 1} Λ) ι ιj hdisj M (externalProduct _ (j ≫ b₁) b₂
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj N₁) N₂) n
    @Equiv.subsingleton _ _ ((Iso.refl _).homCongr e₃) this
  have := fun X ↦ isIso_rightDerivedUpperShriekAdjunction_unit_app (ModuleCat.{u + 1} Λ) ι X
  have : IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).unit :=
    NatIso.isIso_of_isIso_app _
  have hF := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι).fullyFaithfulLOfIsIsoUnit
  obtain ⟨e, -⟩ := exists_iso_counit_of_subsingleton
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) ι) hF hFT h₃ ⟨_, ⟨E₁⟩⟩
  exact ⟨hF.preimageIso (e ≪≫ E₁.symm)⟩

end Etale

end AlgebraicGeometry
