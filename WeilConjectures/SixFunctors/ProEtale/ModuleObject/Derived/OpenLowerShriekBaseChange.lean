/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# Extension by zero and base change on bounded constructible module objects

Let `Λ` be a commutative condensed ring. All schemes are separated and of finite type over a
field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all morphisms are morphisms of
`Over (Spec (.of k))`. This file compares the extension by zero `j_!` along open immersions on the
bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` with pullbacks and pushforwards along a
commutative square
```
X' --g'--> X
|          |
j'         j
v          v
Z' --g---> Z
```
with `j` and `j'` open immersions.

* **Base change for extension by zero.** The canonical exchange morphism
  `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`) is an
  isomorphism for a cartesian square
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`).
* **Interchanging proper direct image and extension by zero.** For the inverse of this
  isomorphism, the mate under the adjunctions `Lg'^* ⊣ Rg'_*` and `Lg^* ⊣ Rg_*` is the *exchange
  morphism* `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`, where
  the square is written `IsPullback p i' j p'`). For a cartesian square with `g` proper it is an
  isomorphism, for the coefficient rings `E̲` of a finite extension `E` of `ℚ_ℓ` and `ℚ̲̄_ℓ`
  (`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`):
  this is part (3) of the blueprint lemma `det-sf-comp-composition-interchange`, the input of the
  independence of the lower shriek from the compactification and of its composition law.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange` and, for a
  cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the
  exchange morphism `Rg'_* ⋙ j_! ⟶ j'_! ⋙ Rg_*`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`: base
  change for extension by zero (blueprint `sk-def-sfb-open-base-change`).
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`
  and its `_padicAlgCl` version: interchanging proper direct image and extension by zero
  (blueprint `det-sf-comp-composition-interchange`). The proof restricts to the open `X ⊆ Z`,
  where it is open base change, and to its closed complement, where both sides vanish by proper
  base change (`isIso_boundedConstructibleBaseChange_of_isProper`); it needs the pullback along
  closed immersions and the joint conservativity of the restrictions to an open and its closed
  complement, which are not available for module objects over `Λ`.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change for extension by zero -/

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]



/-- The *unit insertion* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the adjunction
`j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep :
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')

variable {j g j' g'} in
/-- The *square transport* step of the extension-by-zero exchange morphism on bounded
constructible complexes: `Functor.squareTransport` applied to the pullback comparison
`Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square, under `j_!` on the left and `j'_!` on the
right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    (sq : CommSq g' j' j g) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ≅
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq.flip)

/-- The *counit contraction* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ j' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  Functor.whiskerLeft
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit ≫
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
    boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep Λ ℓ j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep Λ ℓ sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep Λ ℓ j g j'

/-- **Base change for extension by zero** on bounded constructible complexes: for a *cartesian*
square with `j` and `j'` open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is
an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) :=
  sorry

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ≅
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)).symm

end BaseChange

/-! ### The exchange morphism -/

section Exchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k

/-- The *unit insertion* step of the exchange morphism: the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p').unit

/-- The *square transport* step of the exchange morphism: `Functor.squareTransport` applied to
the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the cartesian
square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⋙
        (boundedConstructibleUpperStar Λ ℓ p' ⋙ boundedConstructibleLowerStar Λ ℓ p') ≅
      (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
          boundedConstructibleLowerStar Λ ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ p)
    (boundedConstructibleLowerStar Λ ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq)

/-- The *counit contraction* step of the exchange morphism: the natural transformation
`(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of the
adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
          boundedConstructibleLowerStar Λ ℓ p') ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions: the mate, under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep Λ ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep Λ ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep Λ ℓ

end Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExchangeIsIso

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`E`-sheaves (blueprint `det-sf-comp-composition-interchange`, part (3)): the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. Over the
open `X ⊆ Z` it is the identification `Lj^* ⋙ Rp'_* ≅ Rp_* ⋙ Li'^*`, and over the closed
complement `Z ∖ X` the stalks of `Rp'_*(i'_! K)` are, by proper base change, the cohomology of
the fibres of `p'` over `Z ∖ X`, which do not meet `X' ⊆ Z'`, with coefficients in `i'_! K`,
hence vanish. (In the blueprint the square is cartesian by part (1), from the density of `X'`
in `Z'`.) -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.continuousMapRingObj E) ℓ sq) :=
  sorry

/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`ℚ̄_ℓ`-sheaves (blueprint `det-sf-comp-composition-interchange`, part (3)): the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) :=
  sorry

end ExchangeIsIso

end AlgebraicGeometry.ProEtale.CondensedRing
