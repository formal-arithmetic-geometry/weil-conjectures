/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.TraceFormula.Frobenius

/-!

# Integral models for rational Frobenius correspondences

Let `X` be separated of finite type over a field `k` of characteristic `p ≠ ℓ`, `Φ : X ⟶ X` an
endomorphism (the `k`-linear Frobenius of a model over a finite field in the applications),
`E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`K ↦ K_E = E ⊗ᴸ_{𝒪_E} K` for the derived extension of scalars
`ProEtale.boundedConstructibleExtendScalars` from bounded constructible `𝒪_E`-complexes to bounded
constructible `E`-complexes. This file proves blueprint `sk-lem-tf-rational-model`: for every
bounded constructible `E`-complex `K_E` and every *Frobenius correspondence*
`ψ : LΦ^* K_E ⟶ K_E` there are an integral model `K₀` of `K_E`, an integer `N ≥ 0` and an integral
Frobenius correspondence `θ : LΦ^* K₀ ⟶ K₀` with `ℓ^N ψ = θ ⊗ E`
(`ProEtale.CondensedRing.exists_integralModel_frobeniusCorrespondence`). The iterates then satisfy
`ℓ^{N m} ψ_m = θ_m ⊗ E` for every `m` (`ProEtale.CondensedRing.pow_smul_upperStarIterateMap_eq`),
and so do their stalks (`ProEtale.CondensedRing.pow_smul_upperStar_map_upperStarIterateMap_eq`).

## Main definitions

- `ProEtale.CondensedRing.upperStarIterateMap`: the iterate
  `ψ_m : LΦ_m^* K ⟶ K` of a Frobenius correspondence `ψ : LΦ^* K ⟶ K`, for any coefficient ring.
- `ProEtale.CondensedRing.extendScalarsUpperStarIterateIso`: the comparison
  `LΦ_m^* (K_E) ≅ (LΦ_m^* K)_E` assembled from a comparison `σ` for `Φ`.

## Implementation notes

The coefficient comparison `LΦ^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ^*` for the inverse image (blueprint
`sk-prop-scalar-six`, the localization `𝒪_E ⟶ E`) is not part of the library on bounded
constructible complexes; it is an argument `σ` of the statements, which hold for every natural
isomorphism `σ`. The comparisons for the iterates `Φ_m` are assembled from `σ` and the
composition isomorphisms of the inverse image.

The blueprint statement uses the uniformizer `π_E` and writes `ψ_E = π_E^{-N}(θ ⊗ E)`; here the
denominator is a power of `ℓ = π_E^e · u`, `u` a unit of `𝒪_E`, which is equivalent and keeps the
statement inside the `ℤ`-linear structure of the derived categories. The identity for the
operators `T_{c_m}` of blueprint `sk-d-weil` needs the compactly supported operators with `E`- and
`𝒪_E`-coefficients, which the library defines for `ℚ̄_ℓ` only; it follows from the iterate
identity by `𝒪_E`-linearity of `RΓ_c` once these operators are defined.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-! ### Iterates of a Frobenius correspondence -/

section Iterate

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ) (Φ : X ⟶ X)

/-- The derived pullback on bounded constructible complexes is additive, for a coefficient ring of
Deligne's finiteness theorems: it is a left adjoint. -/
instance additive_boundedConstructibleUpperStar_of_isFinitenessCoefficient
    [IsFinitenessCoefficient ℓ Λ] {Y Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (g : Y ⟶ Z) :
    (boundedConstructibleUpperStar Λ ℓ g).Additive := by
  refine ⟨fun {_ _ f f'} ↦ ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ g).homEquiv
    _ _).injective ?_⟩
  simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add,
    Adjunction.unit_naturality, Preadditive.add_comp]

/-- The isomorphism `LΦ_0^* = L(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def upperStarIterateZeroIso :
    boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ 0) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  eqToIso (by rw [frobeniusIterate_zero]) ≪≫ boundedConstructibleUpperStarId Λ ℓ X

/-- The isomorphism `LΦ_{m+1}^* = L(Φ ≫ Φ_m)^* ≅ LΦ_m^* ⋙ LΦ^*`. -/
noncomputable def upperStarIterateSuccIso (m : ℕ) :
    boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ (m + 1)) ≅
      boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ m) ⋙
        boundedConstructibleUpperStar Λ ℓ Φ :=
  eqToIso (by rw [frobeniusIterate_succ]) ≪≫
    boundedConstructibleUpperStarComp Λ ℓ Φ (frobeniusIterate Φ m)

/-- The iterate `ψ_m : LΦ_m^* K ⟶ K` of a Frobenius correspondence `ψ : LΦ^* K ⟶ K`: `ψ_0` is the
identity isomorphism `L(𝟙 X)^* K ≅ K` and `ψ_{m+1}` is the composite
```
LΦ_{m+1}^* K = L(Φ ≫ Φ_m)^* K ≅ LΦ^* LΦ_m^* K --LΦ^* ψ_m--> LΦ^* K --ψ--> K.
```
-/
noncomputable def upperStarIterateMap {K : Dᵇc(X.left)⟦Λ⟧}
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    (m : ℕ) → ((boundedConstructibleUpperStar Λ ℓ (frobeniusIterate Φ m)).obj K ⟶ K)
  | 0 => (upperStarIterateZeroIso ℓ Λ Φ).hom.app K
  | m + 1 =>
    (upperStarIterateSuccIso ℓ Λ Φ m).hom.app K ≫
      (boundedConstructibleUpperStar Λ ℓ Φ).map (upperStarIterateMap ψ m) ≫ ψ

lemma upperStarIterateMap_zero {K : Dᵇc(X.left)⟦Λ⟧}
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) :
    upperStarIterateMap ℓ Λ Φ ψ 0 = (upperStarIterateZeroIso ℓ Λ Φ).hom.app K :=
  rfl

lemma upperStarIterateMap_succ {K : Dᵇc(X.left)⟦Λ⟧}
    (ψ : (boundedConstructibleUpperStar Λ ℓ Φ).obj K ⟶ K) (m : ℕ) :
    upperStarIterateMap ℓ Λ Φ ψ (m + 1) =
      (upperStarIterateSuccIso ℓ Λ Φ m).hom.app K ≫
        (boundedConstructibleUpperStar Λ ℓ Φ).map (upperStarIterateMap ℓ Λ Φ ψ m) ≫ ψ :=
  rfl

end Iterate

/-! ### Integral models -/

section IntegralModel

variable (ℓ) (E : FiniteIntermediateField ℓ) (Φ : X ⟶ X)

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `E`.
set_option quotPrecheck false in
local notation "𝔼" => Profinite.continuousMapRingObj E.1

/-- The comparison `L(𝟙 X)^* ⋙ (-)_E ≅ (-)_E ⋙ L(𝟙 X)^*` for `Φ_0 = 𝟙 X`, through the identity
isomorphisms `L(𝟙 X)^* ≅ 𝟭`. -/
noncomputable def extendScalarsUpperStarIterateZeroIso :
    boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ 0) ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ 0) :=
  Functor.isoWhiskerRight (upperStarIterateZeroIso ℓ 𝒪 Φ)
      (boundedConstructibleExtendScalars X.left ℓ E) ≪≫
    Functor.leftUnitor (boundedConstructibleExtendScalars X.left ℓ E) ≪≫
    (Functor.rightUnitor (boundedConstructibleExtendScalars X.left ℓ E)).symm ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars X.left ℓ E)
      (upperStarIterateZeroIso ℓ 𝔼 Φ).symm

/-- The comparison for `Φ_{m+1}` assembled from comparisons `σ` for `Φ` and `τ` for `Φ_m`:
```
L(Φ ≫ Φ_m)^* ⋙ (-)_E ≅ LΦ_m^* ⋙ LΦ^* ⋙ (-)_E ≅ LΦ_m^* ⋙ (-)_E ⋙ LΦ^*
  ≅ (-)_E ⋙ LΦ_m^* ⋙ LΦ^* ≅ (-)_E ⋙ L(Φ ≫ Φ_m)^*.
```
-/
noncomputable def extendScalarsUpperStarIterateSuccIso
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ)
    (m : ℕ)
    (τ : boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m) ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m)) :
    boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ (m + 1)) ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ (m + 1)) :=
  Functor.isoWhiskerRight (upperStarIterateSuccIso ℓ 𝒪 Φ m)
      (boundedConstructibleExtendScalars X.left ℓ E) ≪≫
    Functor.associator (boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m))
      (boundedConstructibleUpperStar 𝒪 ℓ Φ) (boundedConstructibleExtendScalars X.left ℓ E) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m)) σ ≪≫
    (Functor.associator (boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m))
      (boundedConstructibleExtendScalars X.left ℓ E) (boundedConstructibleUpperStar 𝔼 ℓ Φ)).symm ≪≫
    Functor.isoWhiskerRight τ (boundedConstructibleUpperStar 𝔼 ℓ Φ) ≪≫
    Functor.associator (boundedConstructibleExtendScalars X.left ℓ E)
      (boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m))
      (boundedConstructibleUpperStar 𝔼 ℓ Φ) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars X.left ℓ E)
      (upperStarIterateSuccIso ℓ 𝔼 Φ m).symm

/-- The comparison `LΦ_m^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ_m^*` for the iterates `Φ_m` of `Φ`, assembled
from a comparison `σ` for `Φ` and the composition isomorphisms of the inverse image
(`extendScalarsUpperStarIterateZeroIso`, `extendScalarsUpperStarIterateSuccIso`). -/
noncomputable def extendScalarsUpperStarIterateIso
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ) :
    (m : ℕ) →
      (boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m) ⋙
          boundedConstructibleExtendScalars X.left ℓ E ≅
        boundedConstructibleExtendScalars X.left ℓ E ⋙
          boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m))
  | 0 => extendScalarsUpperStarIterateZeroIso ℓ E Φ
  | m + 1 =>
    extendScalarsUpperStarIterateSuccIso ℓ E Φ σ m (extendScalarsUpperStarIterateIso σ m)


lemma extendScalarsUpperStarIterateZeroIso_inv_app (K₀ : Dᵇc(X.left)⟦𝒪⟧) :
    (extendScalarsUpperStarIterateZeroIso ℓ E Φ).inv.app K₀ =
      (upperStarIterateZeroIso ℓ 𝔼 Φ).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀) ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map
          ((upperStarIterateZeroIso ℓ 𝒪 Φ).inv.app K₀) := by
  simp [extendScalarsUpperStarIterateZeroIso]

lemma extendScalarsUpperStarIterateSuccIso_inv_app
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ)
    (m : ℕ)
    (τ : boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m) ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m)) (K₀ : Dᵇc(X.left)⟦𝒪⟧) :
    (extendScalarsUpperStarIterateSuccIso ℓ E Φ σ m τ).inv.app K₀ =
      (upperStarIterateSuccIso ℓ 𝔼 Φ m).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀) ≫
        (boundedConstructibleUpperStar 𝔼 ℓ Φ).map (τ.inv.app K₀) ≫
        σ.inv.app ((boundedConstructibleUpperStar 𝒪 ℓ (frobeniusIterate Φ m)).obj K₀) ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map
          ((upperStarIterateSuccIso ℓ 𝒪 Φ m).inv.app K₀) := by
  simp [extendScalarsUpperStarIterateSuccIso]

/-- **The iterates of a rational model** (blueprint `sk-lem-tf-rational-model`, (1)): if
`ℓ^N ψ = θ ⊗ E` for a Frobenius correspondence `ψ : LΦ^* K ⟶ K` and an integral Frobenius
correspondence `θ : LΦ^* K₀ ⟶ K₀`, read through `e : (K₀)_E ≅ K` and a comparison `σ`, then
`ℓ^{N m} ψ_m = θ_m ⊗ E` for every `m`, read through `e` and the comparison
`extendScalarsUpperStarIterateIso σ m` for `Φ_m`: the inverse image is additive, so the iterate
of `ℓ^N ψ` is `ℓ^{N m} ψ_m`. -/
theorem pow_smul_upperStarIterateMap_eq
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ)
    {K : Dᵇc(X.left)⟦𝔼⟧} {K₀ : Dᵇc(X.left)⟦𝒪⟧}
    (e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K) {N : ℕ}
    {ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K}
    {θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀}
    (h : ((ℓ : ℤ) ^ N) • ψ =
      (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.inv ≫ σ.inv.app K₀ ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map θ ≫ e.hom)
    (m : ℕ) :
    ((ℓ : ℤ) ^ (N * m)) • upperStarIterateMap ℓ 𝔼 Φ ψ m =
      (boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m)).map e.inv ≫
        (extendScalarsUpperStarIterateIso ℓ E Φ σ m).inv.app K₀ ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map (upperStarIterateMap ℓ 𝒪 Φ θ m) ≫
          e.hom := by
  induction m with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, one_smul, upperStarIterateMap_zero]
    change _ = _ ≫ (extendScalarsUpperStarIterateZeroIso ℓ E Φ).inv.app K₀ ≫ _
    simp only [extendScalarsUpperStarIterateZeroIso_inv_app]
    have h₁ := Iso.map_inv_hom_id_assoc ((upperStarIterateZeroIso ℓ 𝒪 Φ).app K₀)
      (boundedConstructibleExtendScalars X.left ℓ E) e.hom
    simp only [Iso.app_inv, Iso.app_hom] at h₁
    simp only [assoc, h₁]
    have := (upperStarIterateZeroIso ℓ 𝔼 Φ).hom.naturality_assoc e.inv e.hom
    simp only [Functor.id_map, Iso.inv_hom_id, comp_id] at this
    exact this.symm
  | succ m ih =>
    have hsmul : ((ℓ : ℤ) ^ (N * (m + 1))) • upperStarIterateMap ℓ 𝔼 Φ ψ (m + 1) =
        (upperStarIterateSuccIso ℓ 𝔼 Φ m).hom.app K ≫
          (boundedConstructibleUpperStar 𝔼 ℓ Φ).map
            (((ℓ : ℤ) ^ (N * m)) • upperStarIterateMap ℓ 𝔼 Φ ψ m) ≫ (((ℓ : ℤ) ^ N) • ψ) := by
      simp only [upperStarIterateMap_succ, Functor.map_smul, Linear.smul_comp, Linear.comp_smul,
        Linear.comp_smul, smul_smul, ← pow_add, Nat.mul_succ, Nat.add_comm N]
    simp only [hsmul, ih, h]
    change _ = _ ≫ (extendScalarsUpperStarIterateSuccIso ℓ E Φ σ m
      (extendScalarsUpperStarIterateIso ℓ E Φ σ m)).inv.app K₀ ≫ _
    simp only [extendScalarsUpperStarIterateSuccIso_inv_app, upperStarIterateMap_succ]
    have h₁ := fun {Z} (g : _ ⟶ Z) ↦ Iso.map_inv_hom_id_assoc
      ((upperStarIterateSuccIso ℓ 𝒪 Φ m).app K₀) (boundedConstructibleExtendScalars X.left ℓ E) g
    simp only [Iso.app_inv, Iso.app_hom] at h₁
    have h₂ := σ.inv.naturality (upperStarIterateMap ℓ 𝒪 Φ θ m)
    have h₃ := (upperStarIterateSuccIso ℓ 𝔼 Φ m).hom.naturality e.inv
    simp only [Functor.comp_map] at h₂ h₃
    simp only [Functor.map_comp, assoc, Iso.map_hom_inv_id_assoc, h₁, ← reassoc_of% h₂,
      reassoc_of% h₃]

/-- **The stalks of the iterates of a rational model** (blueprint `sk-lem-tf-rational-model`,
(1)): under the hypotheses of `pow_smul_upperStarIterateMap_eq`, for every morphism
`y : T ⟶ X` (a geometric point in the blueprint) with a coefficient comparison `σ_y` for `Ly^*`,
`ℓ^{N m} (ψ_m)_y = (θ_m)_y ⊗ E`, read through `e`, the comparison for `Φ_m` and `σ_y`. -/
theorem pow_smul_upperStar_map_upperStarIterateMap_eq
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ)
    {K : Dᵇc(X.left)⟦𝔼⟧} {K₀ : Dᵇc(X.left)⟦𝒪⟧}
    (e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K) {N : ℕ}
    {ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K}
    {θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀}
    (h : ((ℓ : ℤ) ^ N) • ψ =
      (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.inv ≫ σ.inv.app K₀ ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map θ ≫ e.hom)
    {T : Over (Spec (.of k))} [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom] (y : T ⟶ X)
    (σy : boundedConstructibleUpperStar 𝒪 ℓ y ⋙ boundedConstructibleExtendScalars T.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ y)
    (m : ℕ) :
    ((ℓ : ℤ) ^ (N * m)) • (boundedConstructibleUpperStar 𝔼 ℓ y).map
        (upperStarIterateMap ℓ 𝔼 Φ ψ m) =
      (boundedConstructibleUpperStar 𝔼 ℓ y).map
          ((boundedConstructibleUpperStar 𝔼 ℓ (frobeniusIterate Φ m)).map e.inv ≫
            (extendScalarsUpperStarIterateIso ℓ E Φ σ m).inv.app K₀) ≫
        σy.inv.app _ ≫
        (boundedConstructibleExtendScalars T.left ℓ E).map
          ((boundedConstructibleUpperStar 𝒪 ℓ y).map (upperStarIterateMap ℓ 𝒪 Φ θ m)) ≫
        σy.hom.app K₀ ≫ (boundedConstructibleUpperStar 𝔼 ℓ y).map e.hom := by
  have h₁ := σy.inv.naturality (upperStarIterateMap ℓ 𝒪 Φ θ m)
  simp only [Functor.comp_map] at h₁
  simp only [← Functor.map_smul, pow_smul_upperStarIterateMap_eq ℓ E Φ σ e h m,
    Functor.map_comp, assoc, ← reassoc_of% h₁, Iso.inv_hom_id_app_assoc]

variable [TopologicalSpace.NoetherianSpace X.left]

/-- **Integral models for rational Frobenius correspondences** (blueprint
`sk-lem-tf-rational-model`): let `σ : LΦ^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ^*` be a coefficient comparison for
the inverse image along `Φ` (blueprint `sk-prop-scalar-six`). For every bounded constructible
`E`-complex `K` and every morphism `ψ : LΦ^* K ⟶ K` there are a bounded constructible
`𝒪_E`-complex `K₀`, an isomorphism `e : (K₀)_E ≅ K`, an integer `N ≥ 0` and a Frobenius
correspondence `θ : LΦ^* K₀ ⟶ K₀` such that `ℓ^N ψ = θ ⊗ E`, read through `e` and `σ`.
The iterates and their stalks then satisfy `ℓ^{N m} ψ_m = θ_m ⊗ E`
(`pow_smul_upperStarIterateMap_eq`, `pow_smul_upperStar_map_upperStarIterateMap_eq`).

The integral model `K₀` exists since `(-)_E` is a localization functor (blueprint
`sk-thm-sfb-rationalization-comparison`), and `σ` identifies `LΦ^* K` with `(LΦ^* K₀)_E`; the
localized `Hom` description then writes `ψ` as `ℓ^{-N} (θ ⊗ E)`. -/
theorem exists_integralModel_frobeniusCorrespondence
    (σ : boundedConstructibleUpperStar 𝒪 ℓ Φ ⋙ boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleUpperStar 𝔼 ℓ Φ)
    (K : Dᵇc(X.left)⟦𝔼⟧) (ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K) :
    ∃ (K₀ : Dᵇc(X.left)⟦𝒪⟧) (e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K)
      (N : ℕ) (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀),
      ((ℓ : ℤ) ^ N) • ψ =
        (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.inv ≫ σ.inv.app K₀ ≫
          (boundedConstructibleExtendScalars X.left ℓ E).map θ ≫ e.hom := by
  have hK := ProEtale.exists_boundedConstructibleExtendScalars_obj_iso X.left ℓ E K
  let K₀ := hK.choose
  let e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K := hK.choose_spec.some
  have hθ := ProEtale.exists_pow_smul_eq_boundedConstructibleExtendScalars_map X.left ℓ E
    (σ.hom.app K₀ ≫ (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.hom ≫ ψ ≫ e.inv)
  refine ⟨K₀, e, hθ.choose, hθ.choose_spec.choose, ?_⟩
  symm
  simp only [← hθ.choose_spec.choose_spec, Linear.smul_comp, Linear.comp_smul,
    Iso.inv_hom_id_app_assoc, assoc, Iso.inv_hom_id, comp_id, Iso.map_inv_hom_id_assoc]

end IntegralModel

end AlgebraicGeometry.ProEtale.CondensedRing
