/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

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
`Dj_! ∘ Rg'_* ⟶ Rg''_* ∘ Dj'_!` on unbounded derived categories of étale sheaves. It is the
transpose along the adjunction `Lg''^* ⊣ Rg''_*` of the composite
`Lg''^* ∘ Dj_! ∘ Rg'_* ≅ Dj'_! ∘ Lg'^* ∘ Rg'_* ⟶ Dj'_!` of the derived base change
isomorphism for the extension by zero and the counit of `Lg'^* ⊣ Rg'_*`.

When `g''` is proper, this map is an isomorphism; this is the key step in the proof of the
composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, applied to the cartesian square of
`AlgebraicGeometry.Compactification.isPullback_compRestrict`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange`: the exchange map
  is an isomorphism if `g''` is proper.

## TODO

`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange` is not proved. It
rests on proper base change, which needs torsion coefficients, and on unbounded derived
categories also on finite cohomological dimension; these hypotheses on `A` are still to be
added, as for `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')

/-- **The exchange map of an extension by zero and a derived pushforward**: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the natural
transformation `Dj_! ∘ Rg'_* ⟶ Rg''_* ∘ Dj'_!`, the transpose along `Lg''^* ⊣ Rg''_*` of
`Lg''^* ∘ Dj_! ∘ Rg'_* ≅ Dj'_! ∘ Lg'^* ∘ Rg'_* ⟶ Dj'_!`, where the isomorphism is
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso` and the last map is
the counit of `Lg'^* ⊣ Rg'_*`.

```
  D(U') --Dj'_!--> D(Z')
   |                 |
  Rg'_*     ⇓      Rg''_*
   ↓                 ↓
  D(U) ---Dj_!---> D(Z)
```

(blueprint: `sk-thm-sf-comp-composition`) -/
noncomputable def openImmersionLowerShriekLowerStarExchange :
    R((g')_*[A]) ⋙ D((j)_!open[A]) ⟶ D((j')_!open[A]) ⋙ R((g'')_*[A]) :=
  Functor.whiskerLeft (R((g')_*[A]) ⋙ D((j)_!open[A]))
      (derivedUpperStarLowerStarAdjunction A g'').unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R((g')_*[A]) (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedUpperStarLowerStarAdjunction A g').counit
          D((j')_!open[A]) ≫
        (Functor.leftUnitor _).hom)
      R((g'')_*[A])

lemma openImmersionLowerShriekLowerStarExchange_app
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology A)) :
    (openImmersionLowerShriekLowerStarExchange A hsq).app K =
      (derivedUpperStarLowerStarAdjunction A g'').unit.app (D((j)_!open[A]).obj
          (R((g')_*[A]).obj K)) ≫
        R((g'')_*[A]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app (R((g')_*[A]).obj K) ≫
            D((j')_!open[A]).map ((derivedUpperStarLowerStarAdjunction A g').counit.app K)) := by
  simp [openImmersionLowerShriekLowerStarExchange]

/-- **Proper base change for the extension by zero**: if `g''` is proper, the exchange map
`Dj_! ∘ Rg'_* ⟶ Rg''_* ∘ Dj'_!` is an isomorphism. Over `U` it is the proper base change map
of the cartesian square, and at a geometric point of `Z` outside `U` both sides vanish, since
the fibre of `g''` over it misses `U'`.

Not proved yet: proper base change needs torsion coefficients and, on unbounded derived
categories, finite cohomological dimension. As for
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`, the
hypotheses on `A` are still to be added. -/
instance isIso_openImmersionLowerShriekLowerStarExchange [IsProper g''] :
    IsIso (openImmersionLowerShriekLowerStarExchange A hsq) :=
  sorry

end Etale

end AlgebraicGeometry
