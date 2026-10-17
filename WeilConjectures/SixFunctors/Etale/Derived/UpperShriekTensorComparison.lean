/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-!
# The tensor comparison of the exceptional inverse image

For a morphism `f : X ⟶ Y` admitting a compactification and satisfying the projection formula,
the *tensor comparison* (blueprint `pur9-cs-def-phi`)

`φ_{f,K} : Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`

is the symmetry `Lf^* K ⊗ᴸ ω_f ≅ ω_f ⊗ᴸ Lf^* K` followed by the canonical tensor map
`AlgebraicGeometry.Etale.dualizingComplexTensorMap`, the adjunct under `Rf_! ⊣ Rf^!` of
`Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`. For smooth `f` it is the isomorphism of the
tensor formula of `sk-prop-cohsm`, and it is the last factor of the smooth purity map
(`AlgebraicGeometry.Etale.smoothPurityIso`).

## Main definitions

- `AlgebraicGeometry.Etale.tensorComparison`: `φ_{f,K}`.

## Main statements

- `AlgebraicGeometry.Etale.dualizingComplexTensorMap_naturality`,
  `AlgebraicGeometry.Etale.tensorComparison_naturality`: both maps are natural in `K`.

## Implementation notes

Everything is first proved for an arbitrary coefficient category `A`, and then specialized to
`A = ModuleCat Λ`: at `ModuleCat Λ` the kernel would otherwise have to compare the derived
tensor product with the tensor product of the braided structure of `D(X_ét)` by unfolding both,
which does not terminate in reasonable time.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A f)]

/-- The tensor map `ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is natural in `K`. -/
@[reassoc]
lemma dualizingComplexTensorMapOfIsIso_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : K ⟶ K') :
    ((derivedTensor A X).obj (dualizingComplex A f)).map ((L((f)^*[A])).map g) ≫
        dualizingComplexTensorMapOfIsIso f K' =
      dualizingComplexTensorMapOfIsIso f K ≫ (R(f)^![A]).map g := by
  have h := (rightDerivedUpperShriekAdjunction A f).projectionTensorMap_naturality_right_assoc
    (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M N N' φ ↦ ((projectionMap A f).app M).naturality φ) (𝟙_ _) g
    ((R(f)^![A]).map (λ_ K').hom)
  rw [derivedTensor_obj_map]
  simp only [dualizingComplexTensorMapOfIsIso, rightDerivedUpperShriekTensorMap]
  refine h.trans ?_
  rw [Category.assoc, ← Functor.map_comp, leftUnitor_naturality, Functor.map_comp]

attribute [local instance] derivedBraidedCategory in
/-- The tensor comparison `Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`: the symmetry followed by the tensor map
`AlgebraicGeometry.Etale.dualizingComplexTensorMapOfIsIso`. -/
noncomputable def tensorComparisonOfIsIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A X).obj ((L((f)^*[A])).obj K)).obj (dualizingComplex A f) ⟶
      (R(f)^![A]).obj K :=
  (β_ ((L((f)^*[A])).obj K) (dualizingComplex A f)).hom ≫ dualizingComplexTensorMapOfIsIso f K

attribute [local instance] derivedBraidedCategory in
/-- The tensor comparison is natural in `K`. -/
@[reassoc]
lemma tensorComparisonOfIsIso_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (g : K ⟶ K') :
    ((derivedTensor A X).map ((L((f)^*[A])).map g)).app (dualizingComplex A f) ≫
        tensorComparisonOfIsIso f K' =
      tensorComparisonOfIsIso f K ≫ (R(f)^![A]).map g := by
  simp only [tensorComparisonOfIsIso, Category.assoc,
    ← dualizingComplexTensorMapOfIsIso_naturality, derivedTensor_map_app, derivedTensor_obj_map]
  rw [BraidedCategory.braiding_naturality_left_assoc]

attribute [local instance] derivedBraidedCategory in
/-- The tensor comparison is an isomorphism as soon as the tensor map is one. -/
lemma isIso_tensorComparisonOfIsIso_iff
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (tensorComparisonOfIsIso f K) ↔ IsIso (dualizingComplexTensorMapOfIsIso f K) := by
  rw [tensorComparisonOfIsIso, isIso_comp_left_iff]

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- The canonical tensor map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is natural in `K`. -/
@[reassoc]
lemma dualizingComplexTensorMap_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).map
        ((L((f)^*[ModuleCat.{u + 1} Λ])).map g) ≫ dualizingComplexTensorMap Λ f K' =
      dualizingComplexTensorMap Λ f K ≫ (R(f)^![ModuleCat.{u + 1} Λ]).map g :=
  dualizingComplexTensorMapOfIsIso_naturality f g

/-- Blueprint `pur9-cs-def-phi`: The tensor comparison of a smooth morphism

For `f : X ⟶ Y` admitting a compactification and `K ∈ D(Y_ét, Λ)`, the morphism

`φ_{f,K} : Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`

corresponding under the adjunction `Rf_! ⊣ Rf^!` to

`Rf_!(Lf^* K ⊗ᴸ ω_f) ≅ Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`:

the symmetry, the inverse of the projection map
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`), the counit `ε_f ⊗ 1` of the
adjunction at `Λ_Y`, and the unit isomorphism. It is the symmetry followed by the canonical
tensor map `AlgebraicGeometry.Etale.dualizingComplexTensorMap`, the adjunct of the last three
steps. -/
noncomputable def tensorComparison
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f) ⟶
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K :=
  tensorComparisonOfIsIso f K

/-- The tensor comparison `φ_{f,K}` is natural in `K`. -/
@[reassoc]
lemma tensorComparison_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : K ⟶ K') :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map g)).app
        (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≫ tensorComparison Λ f K' =
      tensorComparison Λ f K ≫ (R(f)^![ModuleCat.{u + 1} Λ]).map g :=
  tensorComparisonOfIsIso_naturality f g

/-- The tensor comparison `φ_{f,K}` is an isomorphism as soon as the tensor map `θ_{f,K}` is
one. -/
lemma isIso_tensorComparison_iff
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorComparison Λ f K) ↔ IsIso (dualizingComplexTensorMap Λ f K) :=
  isIso_tensorComparisonOfIsIso_iff f K

end Etale

end AlgebraicGeometry
