/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!

# Base change for the extension by zero along a cartesian square

Consider a commutative square of schemes

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

with `j` and `j'` open immersions, i.e. `g' ≫ j = j' ≫ g''`. This file constructs the
canonical base change map

`j'_! ∘ g'^* ⟶ g''^* ∘ j_!`

on sheaves for the small étale sites, and proves that it is an isomorphism when the square
is cartesian.

The map is the conjugate, under `j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`,
of the base change map `Etale.baseChangeMap A sq.flip : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the
flipped square. It exists for every commutative square. For a cartesian square it is the
conjugate of an isomorphism by étale base change for the pushforward
(`AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`), hence an isomorphism.

For `g' = 𝟙` this recovers `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange`
(`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap_id_left`).

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`: the base change map
  `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`: **base change for
  the extension by zero**: for a cartesian square, `j'_! g'^* ⟶ g''^* j_!` is an
  isomorphism.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap_id_left`: for `g' = 𝟙` the
  base change map is `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme MorphismProperty Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The base change map for the extension by zero: for a commutative square
`g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

the canonical natural transformation `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`, i.e.
`j'_! g'^* ⟶ g''^* j_!`

```
Sh(U) --g'^*--> Sh(U')
  |                |
 j_!      ⇙      j'_!
  v                v
Sh(Z) --g''^*--> Sh(Z')
```

It is the conjugate of the base change map
`Etale.baseChangeMap A sq.flip : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` under the adjunctions
`j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`.

This map exists for every commutative square, and it runs *against* the direction of the
exchange map `Ex_!` of the blueprint (`sk-def-sf-exchanges`), which is its inverse for a
cartesian square (`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`). -/
noncomputable def Etale.openImmersionLowerShriekBaseChangeMap (sq : CommSq g' j' j g'') :
    (g')^*[A] ⋙ (j')_!open[A] ⟶ (j)_!open[A] ⋙ (g'')^*[A] :=
  (conjugateEquiv ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).comp
      (Etale.upperStarLowerStarAdjunction A g''))
    ((Etale.upperStarLowerStarAdjunction A g').comp
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j'))).symm
    (Etale.baseChangeMap A sq.flip)

/-- **Base change for the extension by zero along a cartesian square**: if the square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions is cartesian, the base change map
`j'_! g'^* ⟶ g''^* j_!` is an isomorphism, being the conjugate of the isomorphism
`Etale.baseChangeMap A hsq.toCommSq.flip`. -/
lemma Etale.isIso_openImmersionLowerShriekBaseChangeMap (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) :=
  have := Etale.isIso_baseChangeMap_flip_of_isPullback A hsq
  conjugateEquiv_symm_iso _ _ _

section IdLeft

/-! ### Comparison with the case `g' = 𝟙` -/

variable {X C D : Scheme.{u}} (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D) (hk : j ≫ q = k)

/-- For the square

```
X --j--> C
|        |
𝟙        q
v        v
X --k--> D
```

the base change map `q_* ⋙ k^* ⟶ j^* ⋙ (𝟙 X)_*` of the flipped square is
`Etale.upperStarBaseChange`, followed by the identification `(𝟙 X)_* ≅ 𝟭` of
`Etale.lowerStarId`. -/
lemma Etale.baseChangeMap_flip_id_left :
    Etale.baseChangeMap A (⟨by simp [hk]⟩ : CommSq (𝟙 X) j k q).flip =
      Etale.upperStarBaseChange A j q k hk ≫ ((j)^*[A]).rightUnitor.inv ≫
        Functor.whiskerLeft (j)^*[A] (Etale.lowerStarId A X).inv := by
  -- Both sides are mates, under `j^* ⊣ j_*` and `k^* ⊣ k_*`, of the composition isomorphism
  -- `j_* ⋙ q_* ≅ k_*`.
  apply (mateEquiv (Etale.upperStarLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A k)).injective
  refine (Etale.mateEquiv_baseChangeSquare A _).trans ?_
  have hR : Etale.upperStarBaseChange A j q k hk ≫ ((j)^*[A]).rightUnitor.inv ≫
        Functor.whiskerLeft (j)^*[A] (Etale.lowerStarId A X).inv =
      ((TwoSquare.mk ((q)_*[A]) ((j)^*[A]) ((k)^*[A]) (𝟭 _)
        (Etale.upperStarBaseChange A j q k hk)).whiskerBottom
          (Etale.lowerStarId A X).inv).natTrans := by
    ext F
    simp [TwoSquare.whiskerBottom]
  rw [hR, mateEquiv_whiskerBottom]
  subst hk
  rw [TwoSquare.whiskerLeft, Etale.mateEquiv_upperStarBaseChange, Etale.squareLowerStarIso,
    Iso.trans_hom, Iso.symm_hom, Etale.lowerStarComp_id_left]
  ext F
  simp

variable [IsOpenImmersion j] [IsOpenImmersion k]

/-- For the square

```
X --j--> C
|        |
𝟙        q
v        v
X --k--> D
```

the base change map `(𝟙 X)^* ⋙ j_! ⟶ k_! ⋙ q^*` is
`Etale.openImmersionLowerShriekBaseChange`, preceded by the identification `(𝟙 X)^* ≅ 𝟭` of
`Etale.upperStarId`. -/
lemma Etale.openImmersionLowerShriekBaseChangeMap_id_left :
    Etale.openImmersionLowerShriekBaseChangeMap A (⟨by simp [hk]⟩ : CommSq (𝟙 X) j k q) =
      Functor.whiskerRight (Etale.upperStarId A X).hom (j)_!open[A] ≫
        ((j)_!open[A]).leftUnitor.hom ≫ Etale.openImmersionLowerShriekBaseChange A j q k hk := by
  have hconj : conjugateEquiv Adjunction.id (Etale.upperStarLowerStarAdjunction A (𝟙 X))
      (Etale.upperStarId A X).hom = (Etale.lowerStarId A X).inv :=
    congrArg Iso.hom (Etale.conjugateIsoEquiv_upperStarId A X)
  have hlu : conjugateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction A j)
      (Adjunction.id.comp (Etale.openImmersionLowerShriekUpperStarAdjunction A j))
      ((j)_!open[A]).leftUnitor.hom = ((j)^*[A]).rightUnitor.inv :=
    conjugateEquiv_leftUnitor_hom _
  rw [Etale.openImmersionLowerShriekBaseChangeMap, Equiv.symm_apply_eq,
    Etale.baseChangeMap_flip_id_left A j q k hk,
    ← conjugateEquiv_comp _
      (Adjunction.id.comp (Etale.openImmersionLowerShriekUpperStarAdjunction A j)) _,
    ← conjugateEquiv_comp _ (Etale.openImmersionLowerShriekUpperStarAdjunction A j) _,
    conjugateEquiv_whiskerRight, hconj, hlu, Etale.openImmersionLowerShriekBaseChange,
    Equiv.apply_symm_apply, Category.assoc]

end IdLeft

end AlgebraicGeometry
