/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

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

recorded as `sq : CommSq g' f' f g`, with noetherian underlying spaces and `f`, `f'` of finite
type. This file constructs the *base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` of module objects over
`Λ_X = p_X^* Λ`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`),
exactly as the étale base-change morphism `Etale.baseChange` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`: it is the composite of
three named transformations, unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction, for the restricted adjunctions
`Lf^* ⊣ Rf_*` on `Dᵇc(-)⟦Λ⟧`.

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

open CategoryTheory Limits TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']

section PullbackComparison

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories, obtained from the
composition isomorphisms `boundedConstructibleUpperStarComp` and the commutativity of the
square. -/
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar Λ g ⋙ boundedConstructibleUpperStar Λ f' ≅
      boundedConstructibleUpperStar Λ f ⋙ boundedConstructibleUpperStar Λ g' :=
  (boundedConstructibleUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ boundedConstructibleUpperStarComp Λ g' f

end PullbackComparison

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType f'] [QuasiCompact f']

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes:
the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ g ⟶
      (boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ g) ⋙
        (boundedConstructibleUpperStar Λ f' ⋙ boundedConstructibleLowerStar Λ f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ g)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes: `Functor.squareTransport` applied to the pullback comparison `θ_sq`, under `Rf_*` on
the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ g) ⋙
        (boundedConstructibleUpperStar Λ f' ⋙ boundedConstructibleLowerStar Λ f') ≅
      (boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ f) ⋙
        (boundedConstructibleUpperStar Λ g' ⋙ boundedConstructibleLowerStar Λ f') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ f)
    (boundedConstructibleLowerStar Λ f') (boundedConstructiblePullbackSquareComparison Λ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes: the natural transformation obtained by contracting the counit of the adjunction
`Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ f) ⋙
        (boundedConstructibleUpperStar Λ g' ⋙ boundedConstructibleLowerStar Λ f') ⟶
      boundedConstructibleUpperStar Λ g' ⋙ boundedConstructibleLowerStar Λ f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ f).counit
    (boundedConstructibleUpperStar Λ g' ⋙ boundedConstructibleLowerStar Λ f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The *base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories of module objects
over `Λ`, assembled as the composite of the unit insertion, the square transport, and the
counit contraction.

Proper base change asserts that this morphism is an isomorphism for a cartesian square with `f`
proper; no such hypothesis is built into the definition. -/
@[no_expose]
noncomputable def boundedConstructibleBaseChange (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStar Λ f ⋙ boundedConstructibleUpperStar Λ g ⟶
      boundedConstructibleUpperStar Λ g' ⋙ boundedConstructibleLowerStar Λ f' :=
  boundedConstructibleBaseChangeUnitStep Λ f g f' ≫
    (boundedConstructibleBaseChangeSquareStep Λ sq).hom ≫
      boundedConstructibleBaseChangeCounitStep Λ f f' g'

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
