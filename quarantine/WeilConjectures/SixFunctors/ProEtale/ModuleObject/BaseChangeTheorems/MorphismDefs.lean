/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.CategoryTheory.AdjunctionSquareExchange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
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

open CategoryTheory in
private lemma triple_app {C D : Type*} [Category C] [Category D]
    {F G H I : C ⥤ D} (p : F ≅ G) (r : F ≅ H) (q : H ≅ I) (K : C) :
    (p.symm ≪≫ r ≪≫ q).app K = (p.app K).symm ≪≫ r.app K ≪≫ q.app K := rfl

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

/-- Component of the pullback-square comparison, before taking its forward map. -/
lemma boundedConstructiblePullbackSquareComparison_app (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left)) :
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).app K =
      ((boundedConstructibleUpperStarComp Λ ℓ f' g).app K).symm ≪≫
        (eqToIso (by simp only [sq.w]) :
          boundedConstructibleUpperStar Λ ℓ (f' ≫ g) ≅
            boundedConstructibleUpperStar Λ ℓ (g' ≫ f)).app K ≪≫
        (boundedConstructibleUpperStarComp Λ ℓ g' f).app K := by
  exact triple_app (boundedConstructibleUpperStarComp Λ ℓ f' g)
    (eqToIso (by simp only [sq.w])) (boundedConstructibleUpperStarComp Λ ℓ g' f) K


end PullbackComparison

section BaseChange

variable [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)


/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes:
the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def boundedConstructibleBaseChangeUnitStep :
    boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStar Λ ℓ f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes: `Functor.squareTransport` applied to the pullback comparison `θ_sq`, under `Rf_*` on
the left and `Rf'_*` on the right. -/
noncomputable def boundedConstructibleBaseChangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStar Λ ℓ f') ≅
      (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ f)
    (boundedConstructibleLowerStar Λ ℓ f') (boundedConstructiblePullbackSquareComparison Λ ℓ sq)

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes: the natural transformation obtained by contracting the counit of the adjunction
`Lf^* ⊣ Rf_*`. -/
noncomputable def boundedConstructibleBaseChangeCounitStep :
    (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') ≫
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
    boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f' :=
  boundedConstructibleBaseChangeUnitStep Λ ℓ f g f' ≫
    (boundedConstructibleBaseChangeSquareStep Λ ℓ sq).hom ≫
      boundedConstructibleBaseChangeCounitStep Λ ℓ f f' g'

variable {f g f' g'} in
private theorem boundedConstructibleBaseChange_def (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      boundedConstructibleBaseChangeUnitStep Λ ℓ f g f' ≫
        (boundedConstructibleBaseChangeSquareStep Λ ℓ sq).hom ≫
          boundedConstructibleBaseChangeCounitStep Λ ℓ f f' g' :=
  rfl

variable {f g f' g'} in
/-- The adjunct presentation is the specified unit--square--counit exchange map. -/
theorem boundedConstructibleBaseChange_eq_unit_square_counit (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      boundedConstructibleBaseChangeUnitStep Λ ℓ f g f' ≫
        (boundedConstructibleBaseChangeSquareStep Λ ℓ sq).hom ≫
          boundedConstructibleBaseChangeCounitStep Λ ℓ f f' g' :=
  boundedConstructibleBaseChange_def Λ ℓ sq

variable {f g f' g'} in
/-- The restricted exchange is the canonical adjunct presentation. -/
theorem boundedConstructibleBaseChange_eq_squareExchange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      Adjunction.squareExchange
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
        (boundedConstructibleUpperStar Λ ℓ g)
        (boundedConstructibleUpperStar Λ ℓ g')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq) := by
  refine (boundedConstructibleBaseChange_eq_unit_square_counit Λ ℓ sq).trans ?_
  exact (Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
    (boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleUpperStar Λ ℓ g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)).symm

-- Match the restricted functors without expanding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison

variable {f g f' g'} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- The adjunct of restricted exchange is the pullback-square comparison and f counit. -/
theorem boundedConstructibleBaseChange_adjunct (sq : CommSq g' f' f g)
    (N : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructibleUpperStar Λ ℓ f').map
        ((boundedConstructibleBaseChange Λ ℓ sq).app N) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').counit.app
        ((boundedConstructibleUpperStar Λ ℓ g').obj N) =
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app
        ((boundedConstructibleLowerStar Λ ℓ f).obj N) ≫
      (boundedConstructibleUpperStar Λ ℓ g').map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit.app N) := by
  rw [boundedConstructibleBaseChange_eq_squareExchange]
  exact Adjunction.squareExchange_map_counit
    (C := ProEtale.BoundedConstructible (condensedRingObj Λ Y.left))
    (D := ProEtale.BoundedConstructible (condensedRingObj Λ X.left))
    (C' := ProEtale.BoundedConstructible (condensedRingObj Λ Y'.left))
    (D' := ProEtale.BoundedConstructible (condensedRingObj Λ X'.left))
    (L := boundedConstructibleUpperStar Λ ℓ f)
    (R := boundedConstructibleLowerStar Λ ℓ f)
    (L' := boundedConstructibleUpperStar Λ ℓ f')
    (R' := boundedConstructibleLowerStar Λ ℓ f')
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
    (boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleUpperStar Λ ℓ g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq) N


variable {f g f' g'} in
/-- The base-change morphism `BC_sq` is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison `θ_sq` under the
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
lemma boundedConstructibleBaseChange_eq_exchangeRight (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq) := by
  unfold boundedConstructibleBaseChange boundedConstructibleBaseChangeUnitStep
    boundedConstructibleBaseChangeSquareStep boundedConstructibleBaseChangeCounitStep
    Adjunction.exchangeRight
  rfl
end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
