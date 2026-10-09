/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp

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

When `g''` is proper and the coefficients are torsion, this map is an isomorphism (stated, not
yet proved); this is the key step in the proof of the composition law `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`: the exchange map
  `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`:
  with torsion coefficients `Λ` and `g''` proper, the exchange map is an isomorphism (not proved
  yet; see its docstring).
- `AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarCompIso`: with torsion coefficients,
  `D(k_!) ⋙ R(r ≫ q)_* ≅ (D(i_!) ⋙ Rp_*) ⋙ (D(j_!) ⋙ Rq_*)` for `k = i ≫ j'` and a cartesian
  square `p ≫ j = j' ≫ r` with `r` proper; this is the composition law of `Rf_!` for
  compatible compactifications.

## TODO

- Prove base change along an open immersion on unbounded derived categories,
  `j^* Rg''_* ≅ Rg'_* j'^*`; it holds for any `g''`, since `j^*` has the exact left adjoint
  `j_!` and so preserves K-injectives.
- Prove that `D(j^*)` of the exchange map agrees with this base change isomorphism, once
  `j^* j_! ≅ 𝟭` and `j'^* j'_! ≅ 𝟭` are used to identify the sources and targets.
- Prove the isomorphism statement
  `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`
  along the plan in its docstring, using the two items above and
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`.
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

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Extension by zero commutes with proper pushforward**: if the coefficient ring `Λ` is
torsion as an additive group, then for a cartesian square `g' ≫ j = j' ≫ g''` of schemes with
`j` and `j'` open immersions and `g''` proper, the exchange map
`Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on the unbounded derived categories `D(-_ét, Λ)` is an
isomorphism.

The statement fails for general coefficients, which is why `Λ` is torsion here. With `Λ` torsion
and `g''` proper it holds by the argument of
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`: the
question is local on `Z`, and over a quasi-compact open of `Z` the proper map `g''` has bounded
fibre dimension, so `Rg''_*` has finite cohomological dimension on torsion sheaves and the
bounded below statement passes to unbounded complexes.

Proof plan: with `i` the closed complement of `j`, it suffices to check the claim after `D(j^*)`
and after `D(i^*)`.
- After `D(j^*)` it follows from base change along the open immersion `j`,
  `j^* Rg''_* ≅ Rg'_* j'^*`, once `j^* j_! ≅ 𝟭` and `j'^* j'_! ≅ 𝟭` identify both sides.
- After `D(i^*)` both sides vanish: the source because `i^* j_! = 0`, and the target by proper
  base change for `g''` along `i`, which is
  `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`, since
  the pullback of `j'_!` to the closed complement of `j'` vanishes.

(blueprint: unbounded analogue of `thm:open-proper-interchange`) -/
theorem isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring
    (hΛ : IsAddTorsion Λ) [IsProper g''] (hsq : IsPullback g' j' j g'') :
    IsIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq) :=
  sorry

/-- **Composition of compactly supported pushforwards along compatible compactifications.**
Let `i : X ⟶ P`, `j' : P ⟶ E`, `j : Y ⟶ Q`, `k : X ⟶ E` be open immersions with
`i ≫ j' = k`, and let `r : E ⟶ Q` be proper, with a cartesian square
```
  P --j'--> E
  |         |
  p         r
  ↓         ↓
  Y --j---> Q --q--> Z
```
For torsion coefficients, `D(k_!) ⋙ R(r ≫ q)_* ≅ (D(i_!) ⋙ Rp_*) ⋙ (D(j_!) ⋙ Rq_*)`. It is
assembled from the composition isomorphisms for `R(-)_*` and for `D(-)_!`, and the inverse of
the exchange map `Rp_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rr_*`, an isomorphism by
`isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring`. When `(i, p)`, `(j, q)`
and `(k, r ≫ q)` are compactifications of `f`, `g` and `f ≫ g`, this is the composition law of
the compactly supported pushforward. -/
noncomputable def openImmersionLowerShriekLowerStarCompIso (hΛ : IsAddTorsion Λ)
    {X P Y E Q Z : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ Y) (j' : P ⟶ E) (j : Y ⟶ Q) (r : E ⟶ Q)
    (q : Q ⟶ Z) (k : X ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsProper r] (hk : i ≫ j' = k) (hsq : IsPullback p j' j r) :
    D((k)_!open[ModuleCat.{u + 1} Λ]) ⋙ R((r ≫ q)_*[ModuleCat.{u + 1} Λ]) ≅
      (D((i)_!open[ModuleCat.{u + 1} Λ]) ⋙ R((p)_*[ModuleCat.{u + 1} Λ])) ⋙
        (D((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ R((q)_*[ModuleCat.{u + 1} Λ])) :=
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring Λ hΛ hsq
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorCompIso' _ _
      (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) r q)).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIsoOfEq (ModuleCat.{u + 1} Λ) hk.symm ≪≫
        openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) i j') ≪≫
      Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

end Etale

end AlgebraicGeometry
