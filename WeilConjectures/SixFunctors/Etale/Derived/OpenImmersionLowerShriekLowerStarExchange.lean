/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange

/-!
# Exchanging an extension by zero with a derived pushforward

For a cartesian square of schemes

```
  U' --j'--> Z'
  |          |
  g'         g''
  ↓          ↓
  U  --j---> Z
```

with `j` and `j'` open immersions, there is a natural exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on unbounded derived categories of étale sheaves. It is the
mate, along the adjunctions `D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the
derived base change isomorphism `D(g'^*) ⋙ Dj'_! ≅ Dj_! ⋙ D(g''^*)` for the extension by zero.
Since the pullbacks are exact, this needs no monoidal structure on the coefficients.

When `g''` is proper and the coefficients are torsion, this map should be an isomorphism; this
is the key step in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## TODO

- Prove base change along an open immersion on unbounded derived categories,
  `j^* Rg''_* ≅ Rg'_* j'^*`; it holds for any `g''`, since `j^*` has the exact left adjoint
  `j_!` and so preserves K-injectives.
- Prove that `D(j^*)` of the exchange map agrees with this base change isomorphism, once
  `j^* j_! ≅ 𝟭` and `j'^* j'_! ≅ 𝟭` are used to identify the sources and targets.
- State and prove that the exchange map is an isomorphism when `g''` is proper. On `D⁺` with
  torsion coefficients this is `thm:open-proper-interchange`. On unbounded derived categories it
  also needs `Rg''_*` to have finite cohomological dimension, because étale topoi are not
  left-complete in general, and that hypothesis still has to be designed. Proof plan: with `i`
  the closed complement of `j`, check the claim after `D(j^*)` and after `D(i^*)`. After
  `D(j^*)` it follows from the two items above. After `D(i^*)` both sides vanish; for the
  target this uses proper base change for `g''` along `i`.
- Redefine `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison` as
  this exchange map for the square `(𝟙 X, c.i, d.i, r.hom)`, whiskered by `R(d.g)_*` and
  composed with `R(𝟙 X)_* ≅ 𝟭` and `R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Its invertibility then
  follows from that of the exchange map, which removes the `sorry` in
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison` in favour
  of the more general statement. This first needs
  `AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso` to be restated as a special
  case of `AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

## Blueprint

This file constructs the map of `thm:open-proper-interchange` on unbounded derived categories.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The exchange map of an extension by zero and a derived pushforward**: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the natural
transformation `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`. It is the mate, along the adjunctions
`D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the base change isomorphism
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

```
  D(U') --Dj'_!--> D(Z')
   |                 |
  Rg'_*     ⇗      Rg''_*
   ↓                 ↓
  D(U) ---Dj_!---> D(Z)
```

The 2-cell goes from the path `Rg'_*` then `Dj_!` (left, then bottom) to the path `Dj'_!` then
`Rg''_*` (top, then right). (blueprint: the map of `thm:open-proper-interchange`, on unbounded
derived categories) -/
noncomputable def openImmersionLowerShriekLowerStarExchange (hsq : IsPullback g' j' j g'') :
    R((g')_*[A]) ⋙ D((j)_!open[A]) ⟶ D((j')_!open[A]) ⋙ R((g'')_*[A]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction A g')
    (mapDerivedUpperStarLowerStarAdjunction A g'')
    (TwoSquare.mk _ _ _ _
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv)).natTrans

/-- The exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` at `K`, written out: the unit of
`D(g''^*) ⊣ Rg''_*`, then the inverse of the base change isomorphism `bc`, then the counit of
`D(g'^*) ⊣ Rg'_*`.

```
  Dj_! Rg'_* K --η--> Rg''_* Dg''^* Dj_! Rg'_* K --Rg''_*(bc⁻¹)--> Rg''_* Dj'_! Dg'^* Rg'_* K
                                                                          |
                                                                   Rg''_* Dj'_!(ε)
                                                                          ↓
                                                                   Rg''_* Dj'_! K
```
-/
@[reassoc]
lemma openImmersionLowerShriekLowerStarExchange_app (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology A)) :
    (openImmersionLowerShriekLowerStarExchange A hsq).app K =
      (mapDerivedUpperStarLowerStarAdjunction A g'').unit.app
          (D((j)_!open[A]).obj (R((g')_*[A]).obj K)) ≫
        R((g'')_*[A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
              (R((g')_*[A]).obj K) ≫
            D((j')_!open[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g').counit.app K)) := by
  simp [openImmersionLowerShriekLowerStarExchange]

end Etale

end AlgebraicGeometry
