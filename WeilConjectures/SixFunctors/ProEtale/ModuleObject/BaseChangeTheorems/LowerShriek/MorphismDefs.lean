/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
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

recorded as `sq : IsPullback g' f' f g`. This file constructs the compact-support base-change
morphisms on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` of module objects over
`Λ_X = p_X^* Λ` (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`).

* **For a compactification.** For a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f` and its base
  change `c.baseChange sq`, a compactification of `f'`, the morphism
  `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.baseChange sq}` (in diagrammatic `⋙`-order), where
  `Rf_!^c := i_! ⋙ Rp_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`),
  exactly as the étale `Etale.lowerShriekBaseChange`. It is the pasting of two exchange
  morphisms:
  - the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper square of the
    base-changed compactification, which is the base-change morphism
    `ProEtale.CondensedRing.boundedConstructibleBaseChange`;
  - the *extension-by-zero exchange* for the open-immersion square of the base-changed
    compactification. Its canonical mate goes in the direction `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*`,
    base change for extension by zero asserts that it is an isomorphism (currently `sorry`),
    and the pasting uses its inverse.
* **For the lower shriek.** For the coefficient rings `E̲` of a finite extension `E` of `ℚ_ℓ` and
  `ℚ̲̄_ℓ`, the morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriek` of the chosen compactifications: the
  pasting for the chosen compactification of `f`, followed by the identification of the lower
  shriek attached to its base change with the lower shriek of `f'`, by the independence of the
  lower shriek from the compactification
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso`).

All schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are over `Spec k`; the compactification `Z` of `f` and `Z ×_Y Y'`
are then so as well (`WeilConjectures.Compactification.Over`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`: the
  canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for a commutative square of open
  immersions, and its three steps; for a cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`:
  the morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.baseChange sq}` for a compactification `c`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`: the morphism
  `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for `E`- and `ℚ̄_ℓ`-sheaves.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`: base
  change for extension by zero.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### For a compactification -/

section Compactification

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

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

/-! ### The compact-support base-change morphism for a compactification -/

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

/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.baseChange sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'`: with
`Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f) (sq : IsPullback g' f' f g) :
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

lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ ℓ k c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ k c.i)
          (boundedConstructibleBaseChange Λ ℓ k (c.baseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ k
            (c.baseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar Λ ℓ k (c.baseChange sq).g) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

end Compactification

/-! ### For the lower shriek -/

section Chosen

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
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

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `E`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into
`Rf'_!^{c_f.baseChange sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ k f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g' ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ k f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ k
      (compactificationOverField k f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E k
      ((compactificationOverField k f).baseChange sq) (compactificationOverField k f')).hom

omit [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] in
lemma boundedConstructibleLowerShriekBaseChange_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange ℓ E k sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ k
          (compactificationOverField k f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E k
          ((compactificationOverField k f).baseChange sq)
          (compactificationOverField k f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange]

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into
`Rf'_!^{c_f.baseChange sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g' ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ k f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ k
      (compactificationOverField k f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ k
      ((compactificationOverField k f).baseChange sq) (compactificationOverField k f')).hom

lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ k sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ k
          (compactificationOverField k f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ k
          ((compactificationOverField k f).baseChange sq)
          (compactificationOverField k f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl]

end Chosen

end AlgebraicGeometry.ProEtale.CondensedRing
