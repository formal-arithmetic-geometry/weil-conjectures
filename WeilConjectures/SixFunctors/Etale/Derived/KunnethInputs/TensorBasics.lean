/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Basic properties of the derived tensor product of étale complexes

Inputs of the ordinary Künneth formula about the derived tensor product `- ⊗ᴸ -` on `D(X_ét)`,
for a monoidal Grothendieck abelian coefficient category `A` with functorial flat resolutions (for
instance `A = ModuleCat Λ`).

## Main results

- `AlgebraicGeometry.Etale.nonempty_derivedTensor_symmetry`.
- `AlgebraicGeometry.Etale.isIso_derivedTensor_unit_constraints`.
- `AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_tensor_comparison`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived tensor product on `D(X_ét)` is symmetric: there
is an isomorphism `K ⊗ᴸ M ≅ M ⊗ᴸ K`, natural in both `K` and `M`, i.e. an isomorphism between the
bifunctor `- ⊗ᴸ -` and its flip. -/
theorem nonempty_derivedTensor_symmetry (X : Scheme.{u}) :
    Nonempty (derivedTensor A X ≅ (derivedTensor A X).flip) :=
  nonempty_iso_derivedTensor_flip A X

/-- The constant sheaf `Λ_X` (the monoidal unit of étale sheaves) placed in degree `0` is the
monoidal unit of `D(X_ét)`. -/
noncomputable def singleFunctorObjTensorUnitIso (X : Scheme.{u}) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj
        (𝟙_ (Sheaf X.smallEtaleTopology A)) ≅
      𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.singleFunctorObjUnitIso _

/-- For `E ∈ D(X_ét)`, the two canonical unit constraints
`E ⊗ᴸ Λ_X ⟶ E` and `Λ_X ⊗ᴸ E ⟶ E` are isomorphisms, where `Λ_X` is the constant sheaf (the
monoidal unit of étale sheaves) placed in degree `0`. -/
theorem isIso_derivedTensor_unit_constraints {X : Scheme.{u}}
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((derivedTensor A X).obj E).map (singleFunctorObjTensorUnitIso A X).hom ≫
        (derivedTensorRightUnitor A X E).hom) ∧
      IsIso (((derivedTensor A X).map (singleFunctorObjTensorUnitIso A X).hom).app E ≫
        (derivedTensorLeftUnitor A X E).hom) :=
  ⟨inferInstance, inferInstance⟩

variable [Etale.UpperStarPreservesFlat A]

/-- For a morphism of schemes `g : Z ⟶ Y`, the
derived pullback is monoidal for the derived tensor product: the canonical comparison
`Lg^*(K ⊗ᴸ L) ⟶ Lg^*K ⊗ᴸ Lg^*L` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`,
natural in `K` and `L`) is an isomorphism, assuming the pullbacks preserve flat sheaves. -/
theorem isIso_leftDerivedUpperStar_tensor_comparison {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (((leftDerivedUpperStarTensorComparison A g).app K).app L) :=
  inferInstance

end Etale

end AlgebraicGeometry
