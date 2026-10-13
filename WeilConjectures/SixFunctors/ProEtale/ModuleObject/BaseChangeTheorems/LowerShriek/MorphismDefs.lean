/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# The compact-support base-change morphism on bounded constructible module objects

Let `Λ` be a commutative condensed ring. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.
This file constructs, on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` of module
objects over `Λ_X = p_X^* Λ`, the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` (in diagrammatic `⋙`-order)

where `c' = c.baseChange sq` is the base-changed compactification of `f'` and
`Rf_!^c := i_! ⋙ Rp_*` is the lower shriek attached to `c`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`, of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), exactly as
the étale `Etale.lowerShriekBaseChange`. It is assembled from two exchange morphisms:

- the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper square of the
  base-changed compactification, which is the base-change morphism
  `ProEtale.CondensedRing.boundedConstructibleBaseChange`;
- the *extension-by-zero exchange* for the open-immersion square of the base-changed
  compactification. Its canonical mate goes in the direction `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`), base
  change for extension by zero asserts that it is an isomorphism (currently `sorry`), and the
  construction of `Ex_!^c` uses its inverse.

The independence of `Ex_!^c` from the chosen compactification is *not* treated here; all
statements are relative to an explicit compactification `c`. All schemes are separated and of
finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all morphisms are over
`Spec k`; the compactification `Z` of `f` and `Z ×_Y Y'` are then so as well
(`WeilConjectures.Compactification.Over`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`: the
  canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for a commutative square of open
  immersions, and its three steps.
- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`:
  base change for extension by zero, for a cartesian square;
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso` is the
  inverse isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange`: the compact-support
  base-change morphism `Ex_!^c`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChangeCompactificationIso`: for a
  cartesian square whose two vertical maps are the same `f`, the identification
  `Rf_!^{c.baseChange sq} ≅ Rf_!^c` of the lower shrieks attached to the base-changed and the
  original compactification.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChangeSelf`: for such a square, the
  compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf_!^c` with the same
  compactification `c` on both sides.

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChangeCompactificationIso`: an
  instance of the independence of the lower shriek from the compactification.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-! ### The extension-by-zero exchange morphism -/

section OpenImmersion

variable {X Z X' Z' : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
  [IsSeparated (Z' ↘ Spec (.of k))]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j'] [j.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [j'.IsOver (Spec (.of k))]
  [g'.IsOver (Spec (.of k))]

/-- The *unit insertion* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the adjunction
`j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep :
    boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j' ⟶
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙
        boundedConstructibleUpperStar Λ ℓ k j) ⋙
        (boundedConstructibleUpperStar Λ ℓ k g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j') :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ k j).unit
    (boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j')

variable {j g j' g'} in
/-- The *square transport* step of the extension-by-zero exchange morphism on bounded
constructible complexes: `Functor.squareTransport` applied to the pullback comparison
`Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square, under `j_!` on the left and `j'_!` on the
right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    (sq : CommSq g' j' j g) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙ boundedConstructibleUpperStar Λ ℓ k j) ⋙
        (boundedConstructibleUpperStar Λ ℓ k g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j') ≅
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙
        boundedConstructibleUpperStar Λ ℓ k g) ⋙
        (boundedConstructibleUpperStar Λ ℓ k j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j') :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j')
    (boundedConstructiblePullbackSquareComparison Λ ℓ k sq.flip)

/-- The *counit contraction* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙ boundedConstructibleUpperStar Λ ℓ k g) ⋙
        (boundedConstructibleUpperStar Λ ℓ k j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙
        boundedConstructibleUpperStar Λ ℓ k g :=
  Functor.whiskerLeft
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙ boundedConstructibleUpperStar Λ ℓ k g)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ k j').counit ≫
    (Functor.rightUnitor _).hom

variable {j g j' g'}

/-- The canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` on bounded constructible
complexes for a commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
of schemes with `j` and `j'` open immersions, assembled as the composite of the unit insertion,
the square transport, and the counit contraction. -/
@[no_expose]
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : CommSq g' j' j g) :
    boundedConstructibleUpperStar Λ ℓ k g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙
        boundedConstructibleUpperStar Λ ℓ k g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep Λ ℓ k j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep Λ ℓ k sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep Λ ℓ k j g j'

/-- **Base change for extension by zero** on bounded constructible complexes: for a *cartesian*
square with `j` and `j'` open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is
an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ k sq.toCommSq) :=
  sorry

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j ⋙ boundedConstructibleUpperStar Λ ℓ k g ≅
      boundedConstructibleUpperStar Λ ℓ k g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ k j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ k sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ k sq.toCommSq)).symm

end OpenImmersion

/-! ### The compact-support base-change morphism -/

section LowerShriek

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
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The *compact-support base-change morphism* `Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` on
bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, where `c' = c.baseChange sq`: with `Rf_!^c = i_! ⋙ Rp_*`, it is
the pasting of the direct-image exchange `boundedConstructibleBaseChange` of the proper square
of the base-changed compactification with the inverse of the extension-by-zero exchange of its
open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`.

The base change theorem for the lower shriek asserts that this morphism is an isomorphism. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k c ⋙
      boundedConstructibleUpperStar Λ ℓ k g ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ k (c.baseChange sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i)
      (boundedConstructibleBaseChange Λ ℓ k (c.baseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ k
        (c.baseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar Λ ℓ k (c.baseChange sq).g) ≫
    (Functor.associator _ _ _).hom

lemma boundedConstructibleLowerShriekBaseChange_eq (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange Λ ℓ k c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i)
          (boundedConstructibleBaseChange Λ ℓ k (c.baseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ k
            (c.baseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar Λ ℓ k (c.baseChange sq).g) ≫
        (Functor.associator _ _ _).hom :=
  by rw [boundedConstructibleLowerShriekBaseChange]

end LowerShriek

/-! ### The base-changed compactification of a square with the same vertical maps -/

section CompactificationIso

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y ⟶ Y} {g' : X ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- For a cartesian square `sq : IsPullback g' f f g` whose two vertical maps are the same
morphism `f`, and a compactification `c` of `f`, the identification
`Rf_!^{c'} ≅ Rf_!^c` on bounded constructible complexes of the lower shriek attached to the
base-changed compactification `c' = c.baseChange sq` with the one attached to `c`. It is the
input that turns the compact-support base-change isomorphism
`Rf_!^c ⋙ Lg^* ≅ Lg'^* ⋙ Rf_!^{c'}` into a commutation isomorphism of `Rf_!^c` with `Lg^*` and
`Lg'^*`, as needed for the Frobenius square of `f` (`g`, `g'` the Frobenius automorphisms).

Both sides are lower shrieks of `f` for two compactifications, so this is an instance of the
independence of the lower shriek from the compactification, which is not formalized; the
isomorphism is currently `sorry`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChangeCompactificationIso
    (c : Compactification f) (sq : IsPullback g' f f g) :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k (c.baseChange sq) ≅
      boundedConstructibleLowerShriekOfCompactification Λ ℓ k c :=
  sorry

/-- The *compact-support base-change morphism* `Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf_!^c` on
bounded constructible complexes for a cartesian square `sq : IsPullback g' f f g` whose two
vertical maps are the same morphism `f`, and a compactification `c` of `f`, with the lower shriek
attached to `c` on both sides: the compact-support base-change morphism
`boundedConstructibleLowerShriekBaseChange` into `Rf_!^{c.baseChange sq}`, followed by the
identification `boundedConstructibleLowerShriekBaseChangeCompactificationIso` of the
base-changed compactification with `c`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChangeSelf (c : Compactification f)
    (sq : IsPullback g' f f g) :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ k c ⋙
        boundedConstructibleUpperStar Λ ℓ k g ⟶
      boundedConstructibleUpperStar Λ ℓ k g' ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ k c :=
  boundedConstructibleLowerShriekBaseChange Λ ℓ k c sq ≫
    Functor.whiskerLeft _
      (boundedConstructibleLowerShriekBaseChangeCompactificationIso Λ ℓ k c sq).hom

lemma boundedConstructibleLowerShriekBaseChangeSelf_eq (c : Compactification f)
    (sq : IsPullback g' f f g) :
    boundedConstructibleLowerShriekBaseChangeSelf Λ ℓ k c sq =
      boundedConstructibleLowerShriekBaseChange Λ ℓ k c sq ≫
        Functor.whiskerLeft _
          (boundedConstructibleLowerShriekBaseChangeCompactificationIso Λ ℓ k c sq).hom := by
  rw [boundedConstructibleLowerShriekBaseChangeSelf]

end CompactificationIso

end AlgebraicGeometry.ProEtale.CondensedRing
