/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.BaseChangeTheorems.MorphismDefs

/-!

# The compact-support base-change morphism on bounded constructible module objects

Let `ℓ` be a prime. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.
This file constructs, on the bounded constructible derived categories `Dᵇc(-)⟦ℚ̄_ℓ⟧` of module
objects over `ℚ̄_ℓ,X`, the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` (in diagrammatic `⋙`-order)

where `c' = c.baseChange sq` is the base-changed compactification of `f'` and
`Rf_!^c := i_! ⋙ Rp_*` is the lower shriek attached to `c`
(`ProEtale.PadicAlgClRing.boundedConstructibleLowerShriekOfCompactification`), exactly as
the étale `Etale.lowerShriekBaseChange`. It is assembled from two exchange morphisms:

- the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper square of the
  base-changed compactification, which is the base-change morphism
  `ProEtale.PadicAlgClRing.boundedConstructibleBaseChange`;
- the *extension-by-zero exchange* for the open-immersion square of the base-changed
  compactification. Its canonical mate goes in the direction `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*`
  (`ProEtale.PadicAlgClRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`), base
  change for extension by zero asserts that it is an isomorphism (currently `sorry`), and the
  construction of `Ex_!^c` uses its inverse.

The independence of `Ex_!^c` from the chosen compactification is *not* treated here; all
statements are relative to an explicit compactification `c`. The noetherianity of the
compactifications `c.Z` and `c'.Z = Z ×_Y Y'` is carried as an instance argument.

## Main definitions

- `ProEtale.PadicAlgClRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`: the
  canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for a commutative square of open
  immersions, and its three steps.
- `ProEtale.PadicAlgClRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`:
  base change for extension by zero, for a cartesian square;
  `ProEtale.PadicAlgClRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso` is the
  inverse isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!`.
- `ProEtale.PadicAlgClRing.boundedConstructibleLowerShriekOfCompactification`: the lower
  shriek `Rf_!^c = i_! ⋙ Rp_*` on `Dᵇc(-)⟦ℚ̄_ℓ⟧` attached to a compactification `c`.
- `ProEtale.PadicAlgClRing.boundedConstructibleLowerShriekBaseChange`: the compact-support
  base-change morphism `Ex_!^c`.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The extension-by-zero exchange morphism -/

section OpenImmersion

variable {X Z X' Z' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Z] [NoetherianSpace X'] [NoetherianSpace Z']
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The *unit insertion* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`Lg'^* ⋙ j'_! ⟶ (j_! ⋙ Lj^*) ⋙ (Lg'^* ⋙ j'_!)` obtained by inserting the unit of the adjunction
`j_! ⊣ Lj^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep :
    boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j' ⟶
      (boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ j) ⋙
        (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j') :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction ℓ j).unit
    (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j')

variable {j g j' g'} in
/-- The *square transport* step of the extension-by-zero exchange morphism on bounded
constructible complexes: `Functor.squareTransport` applied to the pullback comparison
`Lj^* ∘ Lg'^* ≅ Lg^* ∘ Lj'^*` of the square, under `j_!` on the left and `j'_!` on the
right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep
    (sq : CommSq g' j' j g) :
    (boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ j) ⋙
        (boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j') ≅
      (boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g) ⋙
        (boundedConstructibleUpperStar ℓ j' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j') :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek ℓ j)
    (boundedConstructibleOpenImmersionLowerShriek ℓ j')
    (boundedConstructiblePullbackSquareComparison ℓ sq.flip)

/-- The *counit contraction* step of the extension-by-zero exchange morphism on bounded
constructible complexes: the natural transformation
`(j_! ⋙ Lg^*) ⋙ (Lj'^* ⋙ j'_!) ⟶ j_! ⋙ Lg^*` obtained by contracting the counit of the
adjunction `j'_! ⊣ Lj'^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep :
    (boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g) ⋙
        (boundedConstructibleUpperStar ℓ j' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j') ⟶
      boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g :=
  Functor.whiskerLeft
    (boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction ℓ j').counit ≫
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
    boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g :=
  boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep ℓ j j' g' ≫
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep ℓ sq).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep ℓ j g j'

/-- **Base change for extension by zero** on bounded constructible complexes: for a *cartesian*
square with `j` and `j'` open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is
an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange ℓ sq.toCommSq) :=
  sorry

/-- The extension-by-zero exchange isomorphism `j_! ⋙ Lg^* ≅ Lg'^* ⋙ j'_!` on bounded
constructible complexes for a cartesian square of open immersions: the inverse of the canonical
exchange morphism, which is an isomorphism by base change for extension by zero. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
    (sq : IsPullback g' j' j g) :
    boundedConstructibleOpenImmersionLowerShriek ℓ j ⋙ boundedConstructibleUpperStar ℓ g ≅
      boundedConstructibleUpperStar ℓ g' ⋙ boundedConstructibleOpenImmersionLowerShriek ℓ j' :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange ℓ sq
  (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange ℓ sq.toCommSq)).symm

end OpenImmersion

/-! ### The lower shriek attached to a compactification -/

section Compactification

variable {X Y : Scheme.{u}} [NoetherianSpace X] [NoetherianSpace Y] {f : X ⟶ Y}
  (c : Compactification f) [NoetherianSpace c.Z]

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧` on bounded constructible
complexes attached to a compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`: the extension by zero
along the open immersion `i` followed by the derived pushforward along the proper morphism `p`,
both restricted to bounded constructible complexes. It is the bounded constructible incarnation
of `Rf_!(c)⟦ℚ̄_ℓ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.LowerShriek`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification : Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek ℓ c.i ⋙ boundedConstructibleLowerStar ℓ c.g

end Compactification

/-! ### The compact-support base-change morphism -/

section LowerShriek

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

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
    (sq : IsPullback g' f' f g) [NoetherianSpace c.Z] [NoetherianSpace ↥(pullback c.g g)] :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙ boundedConstructibleUpperStar ℓ g ⟶
      boundedConstructibleUpperStar ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ (c.baseChange sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek ℓ c.i)
      (boundedConstructibleBaseChange ℓ (c.baseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso ℓ
        (c.baseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar ℓ (c.baseChange sq).g) ≫
    (Functor.associator _ _ _).hom

lemma boundedConstructibleLowerShriekBaseChange_eq (c : Compactification f)
    (sq : IsPullback g' f' f g) [NoetherianSpace c.Z] [NoetherianSpace ↥(pullback c.g g)] :
    boundedConstructibleLowerShriekBaseChange ℓ c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek ℓ c.i)
          (boundedConstructibleBaseChange ℓ (c.baseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso ℓ
            (c.baseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar ℓ (c.baseChange sq).g) ≫
        (Functor.associator _ _ _).hom :=
  by rw [boundedConstructibleLowerShriekBaseChange]

end LowerShriek

end AlgebraicGeometry.ProEtale.PadicAlgClRing
