/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!

# The base change property and injective acyclicity

Fix a commutative ring `Λ` and a morphism of schemes `f : X ⟶ Y`. This file isolates two
properties of `f`, both quantified over *all* base changes `g : Y' ⟶ Y` of `f`, which the
proof of the proper base change theorem proceeds by:

- `AlgebraicGeometry.Etale.SatisfiesBaseChange`, the property `PBC(f)`: the derived
  base-change morphism of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`
  is an isomorphism at every object of `D⁺(X_ét, Λ)` with torsion cohomology;
- `AlgebraicGeometry.Etale.SatisfiesInjectiveAcyclicity`, the property `IA(f)`: for every
  injective sheaf `I` on `X_ét`, the base changed sheaf `g'^{-1} I` has no higher direct
  images along `f'`.

The two are equivalent for proper `f`
(`AlgebraicGeometry.Etale.satisfiesBaseChange_iff_satisfiesInjectiveAcyclicity`), and the
whole proof of proper base change is carried out on the `IA` side, where the statement is a
vanishing statement about a single sheaf rather than a statement about a complex: `IA`
composes, cancels along proper surjections, and can be checked on geometric stalks.

`PBC` is already known for proper `f`, by
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`; the content of this file and of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` is the road leading
there.

## Main definitions

- `AlgebraicGeometry.Etale.SatisfiesBaseChange`: the property `PBC(f)`.
- `AlgebraicGeometry.Etale.SatisfiesInjectiveAcyclicity`: the property `IA(f)`.

## Main statements

- `AlgebraicGeometry.Etale.satisfiesBaseChange_iff_satisfiesInjectiveAcyclicity`:
  `PBC(f) ↔ IA(f)` for a proper morphism `f`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-def-pbc`: The PBC property.

`PBC(f)` for a morphism of schemes `f : X ⟶ Y`: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and every object `K` of `D⁺(X_ét, Λ)` whose cohomology sheaves are all torsion, the derived
base-change morphism `BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism. No
hypothesis is imposed on `g`, and none on `f`: the proper base change theorem says that
`PBC(f)` holds whenever `f` is proper. -/
def Etale.SatisfiesBaseChange (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄ (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    Etale.DerivedCategory.Plus.torsionHomology Λ X K →
      IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)

/-- Blueprint `sk-def-ia`: Injective acyclicity.

`IA(f)` for a morphism of schemes `f : X ⟶ Y`: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and every *injective* sheaf `I` of `Λ`-modules on `X_ét`, the higher direct images of its
pullback vanish: `Rᵠf'_*(g'^{-1} I) = 0` for `q > 0`. Here `Rᵠf'_* G` is the `q`-th
cohomology sheaf of `Rf'_*` applied to `G` placed in degree `0`.

This is the form in which the proper base change theorem is actually proved: it is a
vanishing statement about a single sheaf, it composes, it cancels along proper surjections,
and it can be checked on geometric stalks. It is equivalent to `PBC(f)` for proper `f`, see
`AlgebraicGeometry.Etale.satisfiesBaseChange_iff_satisfiesInjectiveAcyclicity`. -/
def Etale.SatisfiesInjectiveAcyclicity (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄, IsPullback g' f' f g →
    ∀ (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)), Injective I →
      ∀ q : ℤ, 0 < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          (R+((f')_*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
                ((g')^*[ModuleCat.{u + 1} Λ].obj I))))

/-- Blueprint `sk-thm-iff`: PBC ⟺ IA.

For a proper morphism `f : X ⟶ Y` the two properties of the preceding definitions agree:
the derived base-change morphism is an isomorphism on all torsion cohomology after every
base change if and only if the base changes of injective sheaves have no higher direct
images.

The implication `PBC ⇒ IA` is immediate, since `Rf_* I = f_* I` for `I` injective. The
converse runs an injective resolution `E ⟶ I⁻` through the acyclicity criterion
`CategoryTheory.Functor.nonempty_homologyIso_rightDerived_of_acyclic` on both sides and
compares the two complexes termwise by the underived exchange morphism, which is an
isomorphism because at a geometric point of `Y'` both stalks are sections over the same
proper geometric fibre. -/
theorem Etale.satisfiesBaseChange_iff_satisfiesInjectiveAcyclicity (f : X ⟶ Y) [IsProper f] :
    Etale.SatisfiesBaseChange Λ f ↔ Etale.SatisfiesInjectiveAcyclicity Λ f :=
  sorry

end AlgebraicGeometry
