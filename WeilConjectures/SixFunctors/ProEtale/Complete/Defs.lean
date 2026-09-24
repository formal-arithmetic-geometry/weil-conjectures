/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Localization.Bifunctor
public import Mathlib.CategoryTheory.Localization.Opposite
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!

# The six functors on derived complete pro-étale sheaves

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, with ring of integers
`𝒪_E`. This file introduces the six functors on the categories of derived complete objects

```
  D_comp(X_proét, 𝒪_E)  ⊆  D(X_proét, 𝒪_E)            (integral coefficients)
  D_comp(X_proét, E)    :=  D_comp(X_proét, 𝒪_E) / torsion   (rational coefficients)
```

of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient` and
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient`, for the
pro-étale site `Scheme.ProEt.topology X` of a scheme. It is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Complete.Defs`.

## Integral coefficients

The functors are those of `WeilConjectures.SixFunctors.ProEtale.Derived` for the coefficient
category `ModuleCat 𝒪_E`, transported to `D_comp(-, 𝒪_E)` in one of two ways.

* `Rg_*`, `Rf^!` and `RHom(K, -)` preserve derived complete objects, so they are restricted
  to `D_comp` along `ObjectProperty.lift`.
* `Lg^*`, `Rf_!` and `- ⊗ᴸ -` do *not* preserve derived completeness in general, so they are
  followed by the derived completion
  `DerivedCategoryDerivedCompleteIntegral.completion : D(X_proét, 𝒪_E) ⥤ D_comp(X_proét, 𝒪_E)`,
  the left adjoint of the inclusion. For the tensor product this is the completed tensor
  product `K ⊗̂ᴸ L := (K ⊗ᴸ L)^`.

## Rational coefficients

`D_comp(X_proét, E)` is a localization of `D_comp(X_proét, 𝒪_E)` at the morphisms whose mapping
cone is torsion, so each rational functor is the functor induced, by the universal property
of the localization (`CategoryTheory.Localization.lift` and, for the two bifunctors,
`CategoryTheory.Localization.lift₂`), by the corresponding integral functor followed by the
localization functor `D_comp(-, 𝒪_E) ⥤ D_comp(-, E)`. The integral functors invert these
morphisms because they are `𝒪_E`-linear and triangulated, hence send torsion cones to
torsion cones.

## Main definitions

- `AlgebraicGeometry.ProEtale.integralUpperStar`, `integralLowerStar`, `integralLowerShriek`,
  `integralUpperShriek`, `integralTensor`, `integralHom` : the six functors on
  `D_comp(-, 𝒪_E)`.
- `AlgebraicGeometry.ProEtale.rationalUpperStar`, `rationalLowerStar`, `rationalLowerShriek`,
  `rationalUpperShriek`, `rationalTensor`, `rationalHom` : the six functors on `D_comp(-, E)`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]

section Integral

/-! ## Integral coefficients -/

section UpperLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pullback `g^* : D_comp(Y_proét, 𝒪_E) ⥤ D_comp(Z_proét, 𝒪_E)`: the derived pullback
`Lg^*` followed by the derived completion. -/
noncomputable def integralUpperStar :
    DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Z) l E :=
  DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology Y) l E ⋙
    L((g)^*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]) ⋙
      DerivedCategoryDerivedCompleteIntegral.completion (Scheme.ProEt.topology Z) l E

/-- The derived pushforward `Rg_*` sends derived complete objects to derived complete
objects. -/
lemma derivedCompleteIntegral_rightDerivedLowerStar_obj
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology Z) l E K) :
    DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology Y) l E
      ((R((g)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])).obj K) :=
  sorry

/-- The pushforward `Rg_* : D_comp(Z_proét, 𝒪_E) ⥤ D_comp(Y_proét, 𝒪_E)`: the restriction of the
derived pushforward `R((g)_*[𝒪_E])`, which preserves derived complete objects by
`derivedCompleteIntegral_rightDerivedLowerStar_obj`. -/
noncomputable def integralLowerStar :
    DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Z) l E ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E :=
  (DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology Y) l E).lift
    (DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology Z) l E ⋙
      R((g)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]))
    fun K ↦ derivedCompleteIntegral_rightDerivedLowerStar_obj l E g _ K.property

end UpperLowerStar

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The proper pushforward `Rf_! : D_comp(X_proét, 𝒪_E) ⥤ D_comp(Y_proét, 𝒪_E)`: the derived lower
shriek `R(f)_!` followed by the derived completion. -/
noncomputable def integralLowerShriek :
    DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E :=
  DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology X) l E ⋙
    R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
      DerivedCategoryDerivedCompleteIntegral.completion (Scheme.ProEt.topology Y) l E

/-- The exceptional inverse image `Rf^!` sends derived complete objects to derived complete
objects. -/
lemma derivedCompleteIntegral_rightDerivedUpperShriek_obj
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology Y) l E K) :
    DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology X) l E
      ((R(f)^![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K) :=
  sorry

/-- The exceptional inverse image `Rf^! : D_comp(Y_proét, 𝒪_E) ⥤ D_comp(X_proét, 𝒪_E)`: the
restriction of `R(f)^!`, which preserves derived complete objects by
`derivedCompleteIntegral_rightDerivedUpperShriek_obj`. -/
noncomputable def integralUpperShriek :
    DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E :=
  (DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology X) l E).lift
    (DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology Y) l E ⋙
      R(f)^![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])
    fun K ↦ derivedCompleteIntegral_rightDerivedUpperShriek_obj l E f _ K.property

end Shriek

section TensorHom

variable (X : Scheme.{u})

/-- The completed tensor product `- ⊗̂ᴸ - : D_comp(X_proét, 𝒪_E) ⥤ D_comp(X_proét, 𝒪_E) ⥤
D_comp(X_proét, 𝒪_E)`, `K ⊗̂ᴸ L := (K ⊗ᴸ L)^`: the derived tensor product followed by the
derived completion. -/
noncomputable def integralTensor :
    DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E ⥤
        DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E :=
  DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology X) l E ⋙
    -⊗ᴸ-(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology X) l E) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteIntegral.completion (Scheme.ProEt.topology X) l E)

/-- The derived hom `RHom(K, L)` is derived complete as soon as `L` is. -/
lemma derivedCompleteIntegral_derivedHom_obj
    (K L : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hL : DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology X) l E L) :
    DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology X) l E
      (((RHom(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj
        (Opposite.op K)).obj L) :=
  sorry

/-- The derived hom `RHom(-, -) : D_comp(X_proét, 𝒪_E)ᵒᵖ ⥤ D_comp(X_proét, 𝒪_E) ⥤
D_comp(X_proét, 𝒪_E)`: the restriction of the derived hom `RHom(X)[𝒪_E]`, which takes values
in derived complete objects by `derivedCompleteIntegral_derivedHom_obj`. -/
noncomputable def integralHom :
    (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E)ᵒᵖ ⥤
      DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E ⥤
        DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E :=
  Functor.curry.obj <| (DerivedCategory.derivedCompleteIntegral (Scheme.ProEt.topology X) l E).lift
    (Functor.uncurry.obj
      ((DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology X) l E).op ⋙
        RHom(X)[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))] ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (DerivedCategoryDerivedCompleteIntegral.ι (Scheme.ProEt.topology X) l E)))
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
      (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E)).IsInvertedBy
        (integralUpperStar l E g ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Z) l E) :=
  sorry

/-- The pullback `g^* : D_comp(Y_proét, E) ⥤ D_comp(Z_proét, E)`, induced by `integralUpperStar`
through the universal property of the localization. -/
noncomputable def rationalUpperStar :
    DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Y) l E ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Z) l E :=
  Localization.lift _ (isInvertedBy_integralUpperStar l E g)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Y) l E)

/-- The pushforward `Rg_*` on integral coefficients inverts the morphisms with torsion cone. -/
lemma isInvertedBy_integralLowerStar :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Z) l E)).IsInvertedBy
        (integralLowerStar l E g ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Y) l E) :=
  sorry

/-- The pushforward `Rg_* : D_comp(Z_proét, E) ⥤ D_comp(Y_proét, E)`, induced by `integralLowerStar`
through the universal property of the localization. -/
noncomputable def rationalLowerStar :
    DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Z) l E ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Y) l E :=
  Localization.lift _ (isInvertedBy_integralLowerStar l E g)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Z) l E)

end UpperLowerStar

section Shriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The proper pushforward `Rf_!` on integral coefficients inverts the morphisms with torsion
cone. -/
lemma isInvertedBy_integralLowerShriek :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E)).IsInvertedBy
        (integralLowerShriek l E f ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Y) l E) :=
  sorry

/-- The proper pushforward `Rf_! : D_comp(X_proét, E) ⥤ D_comp(Y_proét, E)`, induced by
`integralLowerShriek` through the universal property of the localization. -/
noncomputable def rationalLowerShriek :
    DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Y) l E :=
  Localization.lift _ (isInvertedBy_integralLowerShriek l E f)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)

/-- The exceptional inverse image `Rf^!` on integral coefficients inverts the morphisms with
torsion cone. -/
lemma isInvertedBy_integralUpperShriek :
    (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
      (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology Y) l E)).IsInvertedBy
        (integralUpperShriek l E f ⋙
          DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E) :=
  sorry

/-- The exceptional inverse image `Rf^! : D_comp(Y_proét, E) ⥤ D_comp(X_proét, E)`, induced by
`integralUpperShriek` through the universal property of the localization. -/
noncomputable def rationalUpperShriek :
    DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology Y) l E ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E :=
  Localization.lift _ (isInvertedBy_integralUpperShriek l E f)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology Y) l E)

end Shriek

section TensorHom

variable (X : Scheme.{u})

/-- The completed tensor product on integral coefficients inverts, in each variable, the
morphisms with torsion cone. -/
lemma isInvertedBy₂_integralTensor :
    MorphismProperty.IsInvertedBy₂
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E))
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E))
      (integralTensor l E X ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)) :=
  sorry

/-- The tensor product `- ⊗̂ᴸ - : D_comp(X_proét, E) ⥤ D_comp(X_proét, E) ⥤ D_comp(X_proét, E)`,
induced by `integralTensor` through the universal property of the localization in two
variables. -/
noncomputable def rationalTensor :
    DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E ⥤
        DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E :=
  Localization.lift₂ _ (isInvertedBy₂_integralTensor l E X)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)

/-- The derived hom on integral coefficients inverts, in each variable, the morphisms with
torsion cone. -/
lemma isInvertedBy₂_integralHom :
    MorphismProperty.IsInvertedBy₂
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E)).op
      (Rationalization.W (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        (DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E))
      (integralHom l E X ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)) :=
  sorry

/-- The derived hom `RHom(-, -) : D_comp(X_proét, E)ᵒᵖ ⥤ D_comp(X_proét, E) ⥤ D_comp(X_proét, E)`,
induced by `integralHom` through the universal property of the localization in two
variables; in the first variable the localization functor is the opposite of
`D_comp(X_proét, 𝒪_E) ⥤ D_comp(X_proét, E)`. -/
noncomputable def rationalHom :
    (DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E)ᵒᵖ ⥤
      DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E ⥤
        DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E :=
  Localization.lift₂ _ (isInvertedBy₂_integralHom l E X)
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E).op
    (DerivedCategoryDerivedCompleteRational.fromIntegral (Scheme.ProEt.topology X) l E)

end TensorHom

end Rational

end ProEtale

end AlgebraicGeometry
