/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Sheaf.CategoryTheory.AdjunctionSquareExchange
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

/-- Component of the pullback-square comparison, before taking its forward map. -/
lemma boundedConstructiblePullbackSquareComparison_app (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq).app K =
      ((boundedConstructibleUpperStarComp Λ ℓ k f' g).app K).symm ≪≫
        (eqToIso (by simp only [sq.w]) :
          boundedConstructibleUpperStar Λ ℓ k (f' ≫ g) ≅
            boundedConstructibleUpperStar Λ ℓ k (g' ≫ f)).app K ≪≫
        (boundedConstructibleUpperStarComp Λ ℓ k g' f).app K := by
  exact triple_app (boundedConstructibleUpperStarComp Λ ℓ k f' g)
    (eqToIso (by simp only [sq.w])) (boundedConstructibleUpperStarComp Λ ℓ k g' f) K


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
  Adjunction.squareExchange
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
    (boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStar Λ ℓ k g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq)

variable {f g f' g'} in
/-- The adjunct presentation is the specified unit--square--counit exchange map. -/
theorem boundedConstructibleBaseChange_eq_unit_square_counit (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ k sq =
      boundedConstructibleBaseChangeUnitStep Λ ℓ k f g f' ≫
        (boundedConstructibleBaseChangeSquareStep Λ ℓ k sq).hom ≫
          boundedConstructibleBaseChangeCounitStep Λ ℓ k f f' g' :=
  Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
    (boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStar Λ ℓ k g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq)

variable {f g f' g'} in
/-- The restricted exchange is the canonical adjunct presentation. -/
theorem boundedConstructibleBaseChange_eq_squareExchange (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ k sq =
      Adjunction.squareExchange
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
        (boundedConstructibleUpperStar Λ ℓ k g)
        (boundedConstructibleUpperStar Λ ℓ k g')
        (boundedConstructiblePullbackSquareComparison Λ ℓ k sq) := by
  refine (boundedConstructibleBaseChange_eq_unit_square_counit Λ ℓ k sq).trans ?_
  exact (Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
    (boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStar Λ ℓ k g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq)).symm

-- Match the restricted functors without expanding their derived implementations.
attribute [local irreducible] boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison

variable {f g f' g'} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- The adjunct of restricted exchange is the pullback-square comparison and f counit. -/
theorem boundedConstructibleBaseChange_adjunct (sq : CommSq g' f' f g)
    (N : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    (boundedConstructibleUpperStar Λ ℓ k f').map
        ((boundedConstructibleBaseChange Λ ℓ k sq).app N) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f').counit.app
        ((boundedConstructibleUpperStar Λ ℓ k g').obj N) =
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq).hom.app
        ((boundedConstructibleLowerStar Λ ℓ k f).obj N) ≫
      (boundedConstructibleUpperStar Λ ℓ k g').map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f).counit.app N) := by
  rw [boundedConstructibleBaseChange_eq_squareExchange]
  exact Adjunction.squareExchange_map_counit
    (C := ProEtale.BoundedConstructible (condensedRingObj Λ Y))
    (D := ProEtale.BoundedConstructible (condensedRingObj Λ X))
    (C' := ProEtale.BoundedConstructible (condensedRingObj Λ Y'))
    (D' := ProEtale.BoundedConstructible (condensedRingObj Λ X'))
    (L := boundedConstructibleUpperStar Λ ℓ k f)
    (R := boundedConstructibleLowerStar Λ ℓ k f)
    (L' := boundedConstructibleUpperStar Λ ℓ k f')
    (R' := boundedConstructibleLowerStar Λ ℓ k f')
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ k f')
    (boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleUpperStar Λ ℓ k g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq) N

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
