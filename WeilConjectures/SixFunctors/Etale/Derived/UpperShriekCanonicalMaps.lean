/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The canonical maps of the exceptional inverse image

For a finite coefficient ring `Λ` and a morphism `f : X ⟶ Y` admitting a compactification, two
canonical morphisms built from the adjunction `Rf_! ⊣ Rf^!`, which enter the definition of a
cohomologically smooth morphism (blueprint `def-pur-co-smoothness`):

* the *tensor map* `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`, where `ω_f = Rf^! Λ_Y`: the adjunct of
  `Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`, the inverse of the projection map
  (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) followed by the counit;
  more generally, the tensor map `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)`;
* the *base change map* `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of a cartesian square
  `g' ≫ f = f' ≫ g`: the mate, under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the
  compact-support base change isomorphism `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and its value
  `Lg'^* ω_f ⟶ ω_{f'}` at `Λ_Y`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`,
  `AlgebraicGeometry.Etale.dualizingComplexTensorMapOfIsIso`: the tensor maps, for any
  coefficients satisfying the projection formula
- `AlgebraicGeometry.Etale.dualizingComplexTensorMap`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`
- `AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Tensor

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A f)]

/-- The **tensor map** `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` of a morphism `f` admitting a
compactification and satisfying the projection formula: the transpose under `Rf_! ⊣ Rf^!` of
`Rf_!(Rf^! M ⊗ᴸ Lf^* N) ≅ Rf_! Rf^! M ⊗ᴸ N ⟶ M ⊗ᴸ N`, the inverse of the projection map
followed by the counit (`CategoryTheory.Adjunction.projectionTensorMap`). -/
noncomputable abbrev rightDerivedUpperShriekTensorMap
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(f)^![A]).obj M ⊗ (L((f)^*[A])).obj N ⟶ (R(f)^![A]).obj (M ⊗ N) :=
  (rightDerivedUpperShriekAdjunction A f).projectionTensorMap
    (fun M N ↦ ((projectionMap A f).app M).app N) M N

/-- The canonical **tensor map** `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` of a morphism `f` admitting
a compactification and satisfying the projection formula, for `ω_f = Rf^! Λ_Y`: the tensor map
`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap` at `(Λ_Y, K)` followed by the left
unitor. -/
noncomputable def dualizingComplexTensorMapOfIsIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (dualizingComplex A f)).obj ((L((f)^*[A])).obj K) ⟶
      (R(f)^![A]).obj K :=
  rightDerivedUpperShriekTensorMap f (𝟙_ _) K ≫ (R(f)^![A]).map (λ_ K).hom

end General

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

instance : IsIso (projectionMap (ModuleCat.{u + 1} Λ) f) :=
  isIso_projectionMap_of_finite Λ f

/-- The canonical **tensor map** `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` (blueprint
`def-pur-co-smoothness`), for `ω_f = Rf^! Λ_Y` and finite coefficients: the adjunct under
`Rf_! ⊣ Rf^!` of `Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`, the inverse of the
projection map (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) followed by the counit
and the left unitor (`AlgebraicGeometry.Etale.dualizingComplexTensorMapOfIsIso`). -/
noncomputable def dualizingComplexTensorMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K :=
  dualizingComplexTensorMapOfIsIso f K

end Tensor

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- The canonical **base change map** `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of a cartesian square
`g' ≫ f = f' ≫ g`

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

the mate, under the adjunctions `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the
compact-support base change isomorphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def rightDerivedUpperShriekBaseChangeMap (sq : IsPullback g' f' f g) :
    R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![ModuleCat.{u + 1} Λ] :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  mateEquiv (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ f')
    (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))

/-- The canonical base change map `Lg'^* ω_f ⟶ ω_{f'}` of the dualizing complexes of a cartesian
square `g' ≫ f = f' ≫ g` (blueprint `def-pur-co-smoothness`): the component of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap` at `Λ_Y`, followed by
`Rf'^!(Lg^* Λ_Y ≅ Λ_{Y'})`. -/
noncomputable def dualizingComplexBaseChangeMap (sq : IsPullback g' f' f g) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ⟶
      dualizingComplex (ModuleCat.{u + 1} Λ) f' :=
  (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
    (R(f')^![ModuleCat.{u + 1} Λ]).map (leftDerivedUpperStarUnitIso _ g).hom

/-- The base change map of the dualizing complexes is an isomorphism as soon as the base change
map of `R^!` is one at `Λ_Y`. -/
lemma isIso_dualizingComplexBaseChangeMap_iff (sq : IsPullback g' f' f g) :
    IsIso (dualizingComplexBaseChangeMap Λ sq) ↔
      IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)) := by
  rw [dualizingComplexBaseChangeMap, isIso_comp_right_iff]

end BaseChange

end Etale

end AlgebraicGeometry
