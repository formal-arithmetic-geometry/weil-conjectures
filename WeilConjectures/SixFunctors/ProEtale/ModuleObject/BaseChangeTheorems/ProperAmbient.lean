/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# The proper base change theorem along an arbitrary base change

Let `Λ` be a commutative condensed ring. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the derived pullbacks are compared by `θ : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*`
(`ProEtale.CondensedRing.leftDerivedUpperStarSquareIso`), the composite of the composition
isomorphisms along `f' ≫ g = g' ≫ f`, and its exchange morphism under the adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` is the base change morphism
`BC : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on the ambient derived categories
(`ProEtale.CondensedRing.leftDerivedBaseChange`).

The proper base change theorem (blueprint `sk-thm-sfb-proper-base-change`) states that `BC` is an
isomorphism on bounded constructible `ℚ̄_ℓ`-complexes when the square is cartesian and `f` is
proper, with no hypothesis on `g`
(`ProEtale.CondensedRing.isIso_leftDerivedBaseChange_app_of_isProper`). Unlike
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`, the schemes
`X'` and `Y'` need not be of finite type over the base field: this covers the base change to an
algebraic closure.

## Sorried input

- `ProEtale.CondensedRing.isIso_leftDerivedBaseChange_app_of_isProper`: the proper base change
  theorem, blueprint `sk-thm-sfb-proper-base-change` (section `sec-six-functors-basics`).

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Square

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The isomorphism `Lt^* ≅ Lt'^*` of the derived pullbacks along equal morphisms, with components
`eqToHom` of equalities of objects. -/
noncomputable def leftDerivedUpperStarCongrIso {A B : Scheme.{u}} {t t' : A ⟶ B} (h : t = t') :
    L((t)^*⟦Λ⟧) ≅ L((t')^*⟦Λ⟧) :=
  NatIso.ofComponents (fun M ↦ eqToIso (congrArg (fun s ↦ L((s)^*⟦Λ⟧).obj M) h))
    (fun φ ↦ by subst h; simp)

/-- The comparison `θ : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of the derived pullbacks along a commutative
square `f' ≫ g = g' ≫ f`: the composite `Lf'^* Lg^* ≅ L(f' ≫ g)^* = L(g' ≫ f)^* ≅ Lg'^* Lf^*`. -/
noncomputable def leftDerivedUpperStarSquareIso (w : f' ≫ g = g' ≫ f) :
    L((g)^*⟦Λ⟧) ⋙ L((f')^*⟦Λ⟧) ≅ L((f)^*⟦Λ⟧) ⋙ L((g')^*⟦Λ⟧) :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫ leftDerivedUpperStarCongrIso Λ w ≪≫
    leftDerivedUpperStarComp Λ g' f

/-- The *base change morphism* `BC : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of a commutative square
`f' ≫ g = g' ≫ f` on the ambient derived categories: the exchange morphism of
`leftDerivedUpperStarSquareIso` under the adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. -/
noncomputable def leftDerivedBaseChange (w : f' ≫ g = g' ≫ f) :
    R((f)_*⟦Λ⟧) ⋙ L((g)^*⟦Λ⟧) ⟶ L((g')^*⟦Λ⟧) ⋙ R((f')_*⟦Λ⟧) :=
  Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (leftDerivedUpperStarSquareIso Λ w)

end Square

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y.left} {f' : X' ⟶ Y'} {g' : X' ⟶ X.left}

include ℓ in
/-- **The proper base change theorem** (blueprint `sk-thm-sfb-proper-base-change`) for bounded
constructible `ℚ̄_ℓ`-complexes, along an arbitrary base change: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` a proper morphism of separated schemes of finite type over a field of characteristic
`p ≠ ℓ`, and `K` a bounded constructible complex on `X`, the base change morphism
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. No hypothesis is imposed on `g`. -/
theorem isIso_leftDerivedBaseChange_app_of_isProper [IsProper f.left]
    (sq : IsPullback g' f' f.left g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K) :
    IsIso ((leftDerivedBaseChange (Profinite.padicAlgClRingObj ℓ) sq.w.symm).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
