/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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
* the *base change map* `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of a cartesian square
  `g' ≫ f = f' ≫ g`: the mate, under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, of the inverse of the
  compact-support base change isomorphism `Ex_! : Rf_! ⋙ Lg^* ≅ Lg'^* ⋙ Rf'_!`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and its value
  `Lg'^* ω_f ⟶ ω_{f'}` at `Λ_Y`.

## Main definitions

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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

instance (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L) :=
  have := isIso_projectionMap_of_finite Λ f
  inferInstance

/-- The adjunct `Rf_!(ω_f ⊗ᴸ Lf^* K) ⟶ K` of the tensor map
`AlgebraicGeometry.Etale.dualizingComplexTensorMap`: the inverse of the projection map
`Rf_! ω_f ⊗ᴸ K ⟶ Rf_!(ω_f ⊗ᴸ Lf^* K)`, followed by the counit `Rf_! ω_f ⟶ Λ_Y` tensored with
`K`, and by the left unitor. -/
noncomputable def dualizingComplexTensorMapAdjunct
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f)_![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶
      K :=
  inv (((projectionMap (ModuleCat.{u + 1} Λ) f).app
      (dualizingComplex (ModuleCat.{u + 1} Λ) f)).app K) ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _))).app K ≫
    (derivedTensorLeftUnitor _ Y K).hom

/-- The canonical **tensor map** `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` (blueprint
`def-pur-co-smoothness`), for `ω_f = Rf^! Λ_Y`: the adjunct under `Rf_! ⊣ Rf^!` of
`Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMapAdjunct`). -/
noncomputable def dualizingComplexTensorMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶
      (R(f)^![ModuleCat.{u + 1} Λ]).obj K :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
    (dualizingComplexTensorMapAdjunct Λ f K)

lemma rightDerivedUpperShriekAdjunction_homEquiv_symm_dualizingComplexTensorMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm
        (dualizingComplexTensorMap Λ f K) = dualizingComplexTensorMapAdjunct Λ f K :=
  Equiv.symm_apply_apply _ _

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
