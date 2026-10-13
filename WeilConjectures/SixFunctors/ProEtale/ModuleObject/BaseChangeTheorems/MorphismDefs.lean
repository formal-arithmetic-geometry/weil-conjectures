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

recorded as `sq : CommSq g' f' f g`, of schemes separated and of finite type over a field `k` of
characteristic `p > 0` with `p ≠ ℓ` and of morphisms over `Spec k`, as for the bounded
constructible six functors. This file constructs the *base-change morphism*

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

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]

include ℓ k

section PullbackComparison

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes on the bounded constructible derived categories, obtained from the
composition isomorphisms `boundedConstructibleUpperStarComp` and the commutativity of the
square. -/
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar Λ ℓ k g ⋙ boundedConstructibleUpperStar Λ ℓ k f' ≅
      boundedConstructibleUpperStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g' :=
  (boundedConstructibleUpperStarComp Λ ℓ k f' g).symm ≪≫
    eqToIso (by simp only [sq.w]) ≪≫ boundedConstructibleUpperStarComp Λ ℓ k g' f

end PullbackComparison

section BaseChange

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes:
the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g ⟶
      (boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g) ⋙
        (boundedConstructibleUpperStar Λ ℓ k f' ⋙ boundedConstructibleLowerStar Λ ℓ k f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes: `Functor.squareTransport` applied to the pullback comparison `θ_sq`, under `Rf_*` on
the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g) ⋙
        (boundedConstructibleUpperStar Λ ℓ k f' ⋙ boundedConstructibleLowerStar Λ ℓ k f') ≅
      (boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k f) ⋙
        (boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ k f)
    (boundedConstructibleLowerStar Λ ℓ k f') (boundedConstructiblePullbackSquareComparison Λ ℓ k sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes: the natural transformation obtained by contracting the counit of the adjunction
`Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k f) ⋙
        (boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f') ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f).counit
    (boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f') ≫
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
    boundedConstructibleLowerStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleLowerStar Λ ℓ k f' :=
  boundedConstructibleBaseChangeUnitStep Λ ℓ k f g f' ≫
    (boundedConstructibleBaseChangeSquareStep Λ ℓ k sq).hom ≫
      boundedConstructibleBaseChangeCounitStep Λ ℓ k f f' g'

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
