/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.BoundedConstructible

/-!

# The base-change morphism on bounded constructible module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime. Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`, with noetherian underlying spaces and `f`, `f'` of finite
type. This file constructs the *base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded constructible derived categories `Dᵇc(-)⟦ℚ̄_ℓ⟧` of module objects over
`ℚ̄_ℓ,X`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.BoundedConstructible`),
exactly as the étale base-change morphism `Etale.baseChange` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`: it is the composite of
three named transformations, unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction, for the restricted adjunctions
`Lf^* ⊣ Rf_*` on `Dᵇc(-)⟦ℚ̄_ℓ⟧`.

The pullback comparison is built from the composition isomorphisms
`ProEtale.PadicAlgClRing.boundedConstructibleUpperStarComp`, which come from the levelwise
functors `D((h)^*⟦ℚ̄_ℓ⟧)` since the pullback on module objects is (assumed) exact.

## Main definitions

- `ProEtale.PadicAlgClRing.boundedConstructiblePullbackSquareComparison`: the pullback
  comparison `θ_sq` of a commutative square on `Dᵇc(-)⟦ℚ̄_ℓ⟧`.
- `ProEtale.PadicAlgClRing.boundedConstructibleBaseChangeUnitStep`,
  `ProEtale.PadicAlgClRing.boundedConstructibleBaseChangeSquareStep`,
  `ProEtale.PadicAlgClRing.boundedConstructibleBaseChangeCounitStep`: the three steps.
- `ProEtale.PadicAlgClRing.boundedConstructibleBaseChange`: the base-change morphism `BC_sq`.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']

section PullbackComparison

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories, obtained from the
composition isomorphisms `boundedConstructibleUpperStarComp` and the commutativity of the
square. -/
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar ℓ g ⋙ boundedConstructibleUpperStar ℓ f' ≅
      boundedConstructibleUpperStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g' :=
  (boundedConstructibleUpperStarComp ℓ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ boundedConstructibleUpperStarComp ℓ g' f

end PullbackComparison

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType f'] [QuasiCompact f']

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes:
the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g ⟶
      (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g) ⋙
        (boundedConstructibleUpperStar ℓ f' ⋙ boundedConstructibleLowerStar ℓ f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes: `Functor.squareTransport` applied to the pullback comparison `θ_sq`, under `Rf_*` on
the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g) ⋙
        (boundedConstructibleUpperStar ℓ f' ⋙ boundedConstructibleLowerStar ℓ f') ≅
      (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ f) ⋙
        (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleLowerStar ℓ f') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ f)
    (boundedConstructibleLowerStar ℓ f') (boundedConstructiblePullbackSquareComparison ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes: the natural transformation obtained by contracting the counit of the adjunction
`Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ f) ⋙
        (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleLowerStar ℓ f') ⟶
      boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleLowerStar ℓ f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ f).counit
    (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleLowerStar ℓ f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `ℚ̄_ℓ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction.

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleUpperStar ℓ g ⟶
      boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleLowerStar ℓ f' :=
  boundedConstructibleBaseChangeUnitStep ℓ f g f' ≫
    (boundedConstructibleBaseChangeSquareStep ℓ sq).hom ≫
      boundedConstructibleBaseChangeCounitStep ℓ f f' g'

end BaseChange

end AlgebraicGeometry.ProEtale.PadicAlgClRing
