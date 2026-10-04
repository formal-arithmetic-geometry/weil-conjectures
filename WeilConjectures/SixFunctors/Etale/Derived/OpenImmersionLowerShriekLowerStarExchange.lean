/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

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

When `g''` is proper and the coefficients are torsion, this map is an isomorphism; this is the
key step in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, applied to the
cartesian square of `AlgebraicGeometry.Compactification.isPullback_restrict`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange`: the exchange map
  is an isomorphism if `g''` is proper and the coefficient ring is torsion.

## TODO

- Prove `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange`; the plan is
  recorded in its proof.
- The comparison `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`
  along a refinement is this exchange map for the square `(𝟙 X, c.i, d.i, r.hom)`, whiskered
  by `R(d.g)_*` and composed with `R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`, up to the
  identifications `R(𝟙 X)_* ≅ 𝟭` and `D(𝟙 X^*) ≅ 𝟭`.
  Prove this identification, so that its invertibility follows from
  `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange`.

## Blueprint

This file implements the unbounded analogue of `thm:open-proper-interchange`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Exchange

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')

/-- **The exchange map of an extension by zero and a derived pushforward**: for a cartesian
square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the natural
transformation `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`. It is the mate, along the adjunctions
`D(g'^*) ⊣ Rg'_*` and `D(g''^*) ⊣ Rg''_*`, of the inverse of the base change isomorphism
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.

```
  D(U') --Dj'_!--> D(Z')
   |                 |
  Rg'_*     ⇓      Rg''_*
   ↓                 ↓
  D(U) ---Dj_!---> D(Z)
```

(blueprint: unbounded analogue of `thm:open-proper-interchange`) -/
noncomputable def openImmersionLowerShriekLowerStarExchange :
    R((g')_*[A]) ⋙ D((j)_!open[A]) ⟶ D((j')_!open[A]) ⋙ R((g'')_*[A]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction A g')
    (mapDerivedUpperStarLowerStarAdjunction A g'')
    (.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv)).natTrans

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
lemma openImmersionLowerShriekLowerStarExchange_app
    (K : DerivedCategory (Sheaf U'.smallEtaleTopology A)) :
    (openImmersionLowerShriekLowerStarExchange A hsq).app K =
      (mapDerivedUpperStarLowerStarAdjunction A g'').unit.app
          (D((j)_!open[A]).obj (R((g')_*[A]).obj K)) ≫
        R((g'')_*[A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).inv.app
              (R((g')_*[A]).obj K) ≫
            D((j')_!open[A]).map ((mapDerivedUpperStarLowerStarAdjunction A g').counit.app K)) := by
  simp [openImmersionLowerShriekLowerStarExchange]

end Exchange

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'')

/-- **Proper base change for the extension by zero**: if `g''` is proper and the coefficient
ring `Λ` is torsion as an additive group, the exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` is
an isomorphism on the unbounded derived categories of étale sheaves of `Λ`-modules.
(blueprint: unbounded analogue of `thm:open-proper-interchange`) -/
theorem isIso_openImmersionLowerShriekLowerStarExchange (hΛ : IsAddTorsion Λ) [IsProper g''] :
    IsIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq) := by
  -- Proof plan. Let `i := j.closedComplement` and `i' : Z'_∖U' ⟶ Z'` its base change along
  -- `g''`. By `AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map` it
  -- suffices to check that `D(j^*)` and `D(i^*)` of the map are invertible.
  -- * `D(i^*)`: the source `i^* Dj_! Rg'_* K` vanishes by
  --   `isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range`; the
  --   target `i^* Rg''_* Dj'_! K ≅ Rg'''_* i'^* Dj'_! K` vanishes by proper base change
  --   `isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring` for `g''` along `i`, and the
  --   same vanishing for `i'^* Dj'_!`.
  -- * `D(j^*)`: by base change for `g''` along the open immersion `j`, which is still missing on
  --   unbounded derived categories, the map becomes the identity of `Rg'_* K`.
  sorry

end Etale

/-! ### Axiom census

The exchange map is built from the levelwise pullbacks and is unconditional; the check below is
run by the build, so a `sorry` reappearing beneath it breaks compilation. -/

/--
info: 'AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange

end AlgebraicGeometry
