/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.Opposite
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!

# The six functors on derived complete étale sheaves

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, with ring of integers
`𝒪_E`. This file introduces the six functors on the categories of derived complete objects

```
  D_comp(X_ét, 𝒪_E)  ⊆  D(X_ét, 𝒪_E)            (integral coefficients)
  D_comp(X_ét, E)    :=  D_comp(X_ét, 𝒪_E) / torsion   (rational coefficients)
```

of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient` and
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient`, for the small
étale site of a scheme.

## Integral coefficients

The functors are those of `WeilConjectures.SixFunctors.Etale.Derived` for the coefficient
category `ModuleCat 𝒪_E`, transported to `D_comp(-, 𝒪_E)` in one of two ways.

* `Rg_*`, `Rf^!` and `RHom(K, -)` preserve derived complete objects, so they are restricted
  to `D_comp` along `ObjectProperty.lift`.
* `Lg^*`, `Rf_!` and `- ⊗ᴸ -` do *not* preserve derived completeness in general, so they are
  followed by the derived completion
  `DerivedCategoryDerivedCompleteIntegral.completion : D(X_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`,
  the left adjoint of the inclusion. For the tensor product this is the completed tensor
  product `K ⊗̂ᴸ L := (K ⊗ᴸ L)^`.

## Rational coefficients

`D_comp(X_ét, E)` is a localization of `D_comp(X_ét, 𝒪_E)` at the morphisms whose mapping
cone is torsion, so each rational functor is the functor induced, by the universal property
of the localization (`CategoryTheory.Localization.lift` and, for the two bifunctors,
`CategoryTheory.Localization.lift₂`), by the corresponding integral functor followed by the
localization functor `D_comp(-, 𝒪_E) ⥤ D_comp(-, E)`. The integral functors invert these
morphisms because they are `𝒪_E`-linear and triangulated, hence send torsion cones to
torsion cones.

## Main definitions

- `AlgebraicGeometry.Etale.integralUpperStar`, `integralLowerStar`, `integralLowerShriek`,
  `integralUpperShriek`, `integralTensor`, `integralHom` : the six functors on
  `D_comp(-, 𝒪_E)`.
- `AlgebraicGeometry.Etale.rationalUpperStar`, `rationalLowerStar`, `rationalLowerShriek`,
  `rationalUpperShriek`, `rationalTensor`, `rationalHom` : the six functors on `D_comp(-, E)`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]


section Integral

/-! ## Integral coefficients -/

section UpperLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pullback `g^* : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(Z_ét, 𝒪_E)`: the derived pullback
`Lg^*` followed by the derived completion. -/
noncomputable def integralUpperStar :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E :=
  DerivedCategoryDerivedCompleteIntegral.ι Y.smallEtaleTopology l E ⋙
    L((g)^*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]) ⋙
      DerivedCategoryDerivedCompleteIntegral.completion Z.smallEtaleTopology l E

/-- The derived pushforward `Rg_*` sends derived complete objects to derived complete
objects. -/
lemma derivedCompleteIntegral_rightDerivedLowerStar_obj
    (K : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral Z.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R((g)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])).obj K) :=
  sorry

/-- The pushforward `Rg_* : D_comp(Z_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_E)`: the restriction of the
derived pushforward `R((g)_*[𝒪_E])`, which preserves derived complete objects by
`derivedCompleteIntegral_rightDerivedLowerStar_obj`. -/
noncomputable def integralLowerStar :
    DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E :=
  (DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).lift
    (DerivedCategoryDerivedCompleteIntegral.ι Z.smallEtaleTopology l E ⋙
      R((g)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]))
    fun K ↦ derivedCompleteIntegral_rightDerivedLowerStar_obj l E g _ K.property

end UpperLowerStar

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The proper pushforward `Rf_! : D_comp(X_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_E)`: the derived lower
shriek `R(f)_!` followed by the derived completion. -/
noncomputable def integralLowerShriek :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E :=
  DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E ⋙
    R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
      DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E

/-- The exceptional inverse image `Rf^!` sends derived complete objects to derived complete
objects. -/
lemma derivedCompleteIntegral_rightDerivedUpperShriek_obj
    (K : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((R(f)^![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K) :=
  sorry

/-- The exceptional inverse image `Rf^! : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`: the
restriction of `R(f)^!`, which preserves derived complete objects by
`derivedCompleteIntegral_rightDerivedUpperShriek_obj`. -/
noncomputable def integralUpperShriek :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    (DerivedCategoryDerivedCompleteIntegral.ι Y.smallEtaleTopology l E ⋙
      R(f)^![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])
    fun K ↦ derivedCompleteIntegral_rightDerivedUpperShriek_obj l E f _ K.property

end Shriek

section TensorHom

variable (X : Scheme.{u})

/-- The completed tensor product `- ⊗̂ᴸ - : D_comp(X_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E) ⥤
D_comp(X_ét, 𝒪_E)`, `K ⊗̂ᴸ L := (K ⊗ᴸ L)^`: the derived tensor product followed by the
derived completion. -/
noncomputable def integralTensor :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
        DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E ⋙
    -⊗ᴸ-(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteIntegral.completion X.smallEtaleTopology l E)

/-- The derived hom `RHom(K, L)` is derived complete as soon as `L` is. -/
lemma derivedCompleteIntegral_derivedHom_obj
    (K L : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hL : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E L) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      (((RHom(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj
        (Opposite.op K)).obj L) :=
  sorry

/-- The derived hom `RHom(-, -) : D_comp(X_ét, 𝒪_E)ᵒᵖ ⥤ D_comp(X_ét, 𝒪_E) ⥤
D_comp(X_ét, 𝒪_E)`: the restriction of the derived hom `RHom(X)[𝒪_E]`, which takes values in
derived complete objects by `derivedCompleteIntegral_derivedHom_obj`. -/
noncomputable def integralHom :
    (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E)ᵒᵖ ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
        DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  Functor.curry.obj <| (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    (Functor.uncurry.obj ((DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E).op ⋙
      RHom(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E)))
    fun KL ↦ derivedCompleteIntegral_derivedHom_obj l E X _ _ KL.2.property

end TensorHom

end Integral

section Rational

/-! ## Rational coefficients -/

section UpperLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pullback `g^*` on integral coefficients inverts the morphisms with torsion cone. -/
lemma isInvertedBy_integralUpperStar :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E)).IsInvertedBy
        (integralUpperStar l E g ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral Z.smallEtaleTopology l E) :=
  sorry

/-- The pullback `g^* : D_comp(Y_ét, E) ⥤ D_comp(Z_ét, E)`, induced by `integralUpperStar`
through the universal property of the localization. -/
noncomputable def rationalUpperStar :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E :=
  Localization.lift _ (isInvertedBy_integralUpperStar l E g)
    (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E)

/-- The pushforward `Rg_*` on integral coefficients inverts the morphisms with torsion cone. -/
lemma isInvertedBy_integralLowerStar :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E)).IsInvertedBy
        (integralLowerStar l E g ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E) :=
  sorry

/-- The pushforward `Rg_* : D_comp(Z_ét, E) ⥤ D_comp(Y_ét, E)`, induced by `integralLowerStar`
through the universal property of the localization. -/
noncomputable def rationalLowerStar :
    DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E :=
  Localization.lift _ (isInvertedBy_integralLowerStar l E g)
    (DerivedCategoryDerivedCompleteRational.fromIntegral Z.smallEtaleTopology l E)

end UpperLowerStar

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The proper pushforward `Rf_!` on integral coefficients inverts the morphisms with torsion
cone. -/
lemma isInvertedBy_integralLowerShriek :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E)).IsInvertedBy
        (integralLowerShriek l E f ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E) :=
  sorry

/-- The proper pushforward `Rf_! : D_comp(X_ét, E) ⥤ D_comp(Y_ét, E)`, induced by
`integralLowerShriek` through the universal property of the localization. -/
noncomputable def rationalLowerShriek :
    DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E :=
  Localization.lift _ (isInvertedBy_integralLowerShriek l E f)
    (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)

/-- The exceptional inverse image `Rf^!` on integral coefficients inverts the morphisms with
torsion cone. -/
lemma isInvertedBy_integralUpperShriek :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E)).IsInvertedBy
        (integralUpperShriek l E f ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E) :=
  sorry

/-- The exceptional inverse image `Rf^! : D_comp(Y_ét, E) ⥤ D_comp(X_ét, E)`, induced by
`integralUpperShriek` through the universal property of the localization. -/
noncomputable def rationalUpperShriek :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Localization.lift _ (isInvertedBy_integralUpperShriek l E f)
    (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E)

end Shriek

section TensorHom

variable (X : Scheme.{u})

/-- The completed tensor product on integral coefficients inverts, in each variable, the
morphisms with torsion cone. -/
lemma isInvertedBy₂_integralTensor :
    MorphismProperty.IsInvertedBy₂
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E))
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E))
      (integralTensor l E X ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)) :=
  sorry

/-- The tensor product `- ⊗̂ᴸ - : D_comp(X_ét, E) ⥤ D_comp(X_ét, E) ⥤ D_comp(X_ét, E)`,
induced by `integralTensor` through the universal property of the localization in two
variables. -/
noncomputable def rationalTensor :
    DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
        DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Localization.lift₂ _ (isInvertedBy₂_integralTensor l E X)
    (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)
    (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)

/-- The derived hom on integral coefficients inverts, in each variable, the morphisms with
torsion cone. -/
lemma isInvertedBy₂_integralHom :
    MorphismProperty.IsInvertedBy₂
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E)).op
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E))
      (integralHom l E X ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)) :=
  sorry

/-- The derived hom `RHom(-, -) : D_comp(X_ét, E)ᵒᵖ ⥤ D_comp(X_ét, E) ⥤ D_comp(X_ét, E)`,
induced by `integralHom` through the universal property of the localization in two
variables; in the first variable the localization functor is the opposite of
`D_comp(X_ét, 𝒪_E) ⥤ D_comp(X_ét, E)`. -/
noncomputable def rationalHom :
    (DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E)ᵒᵖ ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
        DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Localization.lift₂ _ (isInvertedBy₂_integralHom l E X)
    (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).op
    (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E)

end TensorHom

end Rational

end Etale

end AlgebraicGeometry
