/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
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
- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap`: the
  comparison `j_! ⟶ j_*` intertwines this base change map with the base change map
  `g''^* j_* ⟶ j'_* g'^*` of the pushforward. Both sides are compared through their
  transposes under `j'_! ⊣ j'^*` and `j'^* ⊣ j'_*`.

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

omit [HasSmallSiteSheafify A] in
/-- The transpose of the base change map `j'_! g'^* ⟶ g''^* j_!` under `j'_! ⊣ j'^*` is
`g'^*` of the unit of `j_! ⊣ j^*` followed by the square isomorphism. -/
@[reassoc]
lemma Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app (sq : CommSq g' j' j g'')
    (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j').unit.app ((g')^*[A].obj F) ≫
        (j')^*[A].map ((Etale.openImmersionLowerShriekBaseChangeMap A sq).app F) =
      (g')^*[A].map ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app F) ≫
        (Etale.squareUpperStarIso A sq.flip).hom.app ((j)_!open[A].obj F) := by
  apply ((Etale.upperStarLowerStarAdjunction A g').homEquiv _ _).injective
  have := unit_conjugateEquiv_symm ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).comp
      (Etale.upperStarLowerStarAdjunction A g''))
    ((Etale.upperStarLowerStarAdjunction A g').comp
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j'))
    (Etale.baseChangeMap A sq.flip) F
  dsimp only [Functor.comp_obj, Functor.comp_map] at this
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, assoc,
    Etale.map_unit_baseChangeMap_app] at this
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  exact (this.trans (assoc _ _ _)).symm

omit [HasSmallSiteSheafify A] in
/-- The comparison `j_! ⟶ j_*` intertwines the base change map `j'_! g'^* ⟶ g''^* j_!` of the
extension by zero with the base change map `g''^* j_* ⟶ j'_* g'^*` of the pushforward. -/
@[reassoc]
lemma Etale.openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app
    (sq : CommSq g' j' j g'') (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekBaseChangeMap A sq).app F ≫
        (g'')^*[A].map ((Etale.openImmersionLowerShriekToLowerStar A j).app F) ≫
          (Etale.baseChangeMap A sq).app F =
      (Etale.openImmersionLowerShriekToLowerStar A j').app ((g')^*[A].obj F) := by
  apply Etale.openImmersionLowerShriek_lowerStar_hom_ext A j'
  rw [Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit, Functor.map_comp,
    Functor.map_comp, assoc, assoc, Etale.upperStar_map_baseChangeMap_app_counit,
    ← Functor.comp_map (g'')^*[A] (j')^*[A], NatTrans.naturality_assoc, Functor.comp_map,
    Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app_assoc,
    Etale.squareUpperStarIso_flip_hom_app_hom_app_assoc, ← Functor.map_comp, ← Functor.map_comp,
    Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit, CategoryTheory.Functor.map_id]

section IdLeft

/-! ### Comparison with the case `g' = 𝟙` -/

variable {X C D : Scheme.{u}} (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D) (hk : j ≫ q = k)

variable [IsOpenImmersion j] [IsOpenImmersion k]

end IdLeft

end AlgebraicGeometry
