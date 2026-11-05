/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!

# The base-change morphism on bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring. Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`, of schemes separated and of finite type over a field `k` of
characteristic `p > 0` with `p ≠ ℓ` and of morphisms of `Over (Spec (.of k))`, as for the
bounded constructible six functors. This file constructs the *base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` of module objects over
`Λ_X = p_X^* Λ`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`),
exactly as the étale base-change morphism `Etale.baseChange` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`: it is the composite of
three named transformations, unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction, for the restricted adjunctions
`Lf^* ⊣ Rf_*` on `Dᵇc(-)⟦Λ⟧`. As the pushforward on bounded constructible complexes, it is
defined for each of the `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (in the namespaces
`ProEtale.CondensedRing`, `ProEtale.CondensedRing.ContinuousMapRingObj` and
`ProEtale.CondensedRing.PadicIntegersRingObj`); the pullback comparison is stated for a general
`Λ`.

The pullback comparison is built from the composition isomorphisms
`ProEtale.CondensedRing.boundedConstructibleUpperStarComp`, which come from the levelwise
functors `D((h)^*⟦Λ⟧)` since the pullback on module objects is exact.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructiblePullbackSquareComparison`: the pullback
  comparison `θ_sq` of a commutative square on `Dᵇc(-)⟦Λ⟧`.
- `ProEtale.CondensedRing.boundedConstructibleBaseChangeUnitStep`,
  `ProEtale.CondensedRing.boundedConstructibleBaseChangeSquareStep`,
  `ProEtale.CondensedRing.boundedConstructibleBaseChangeCounitStep`: the three steps.
- `ProEtale.CondensedRing.boundedConstructibleBaseChange`: the base-change morphism `BC_sq`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

section PullbackComparison

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories, obtained from the
composition isomorphisms `boundedConstructibleUpperStarComp` and the commutativity of the
square. -/
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ f' ≅
      boundedConstructibleUpperStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g' :=
  (boundedConstructibleUpperStarComp Λ ℓ f' g).symm ≪≫
    eqToIso (by simp only [sq.w]) ≪≫ boundedConstructibleUpperStarComp Λ ℓ g' f

end PullbackComparison

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes
(`ℚ̄_ℓ`-coefficient): the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*`
obtained by inserting the unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes (`ℚ̄_ℓ`-coefficient): `Functor.squareTransport` applied to the pullback comparison `θ_sq`,
under `Rf_*` on the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ f') ≅
      (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ f)
    (boundedConstructibleLowerStar ℓ f') (boundedConstructiblePullbackSquareComparison
      (Profinite.padicAlgClRingObj ℓ) ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes (`ℚ̄_ℓ`-coefficient): the natural transformation obtained by contracting the counit of the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ f') ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
      boundedConstructibleLowerStar ℓ f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction (`ℚ̄_ℓ`-coefficient).

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ f' :=
  boundedConstructibleBaseChangeUnitStep ℓ f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ f f' g'

-- Match the restricted functors without expanding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ f')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl
end BaseChange

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes
(`E`-coefficient): the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained
by inserting the unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ g ⟶
      (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj E) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ E f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes (`E`-coefficient): `Functor.squareTransport` applied to the pullback comparison `θ_sq`,
under `Rf_*` on the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ E f') ≅
      (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
        (Profinite.continuousMapRingObj E) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ E f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ E f)
    (boundedConstructibleLowerStar ℓ E f') (boundedConstructiblePullbackSquareComparison
      (Profinite.continuousMapRingObj E) ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes (`E`-coefficient): the natural transformation obtained by contracting the counit of the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ E f') ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ E f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).counit
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
      boundedConstructibleLowerStar ℓ E f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction (`E`-coefficient).

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ E f' :=
  boundedConstructibleBaseChangeUnitStep ℓ E f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ E sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ E f f' g'

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` (`E`-coefficient). -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ E sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl

end BaseChange

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes
(`𝒪_E`-coefficient): the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained
by inserting the unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ g ⟶
      (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
        (Profinite.padicIntegersRingObj ℓ E) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ E f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes (`𝒪_E`-coefficient): `Functor.squareTransport` applied to the pullback comparison `θ_sq`,
under `Rf_*` on the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ g) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f' ⋙
          boundedConstructibleLowerStar ℓ E f') ≅
      (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
        (Profinite.padicIntegersRingObj ℓ E) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ E f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ E f)
    (boundedConstructibleLowerStar ℓ E f') (boundedConstructiblePullbackSquareComparison
      (Profinite.padicIntegersRingObj ℓ E) ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes (`𝒪_E`-coefficient): the natural transformation obtained by contracting the counit of the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ f) ⋙
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
          boundedConstructibleLowerStar ℓ E f') ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ E f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).counit
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
      boundedConstructibleLowerStar ℓ E f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction (`𝒪_E`-coefficient).

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ E f ⋙ boundedConstructibleUpperStar
      (Profinite.padicIntegersRingObj ℓ E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
        boundedConstructibleLowerStar ℓ E f' :=
  boundedConstructibleBaseChangeUnitStep ℓ E f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ E sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ E f f' g'

variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` (`𝒪_E`-coefficient). -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange ℓ E sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl

end BaseChange

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
