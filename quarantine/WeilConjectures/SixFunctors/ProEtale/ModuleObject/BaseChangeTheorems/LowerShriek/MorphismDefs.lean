/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono
import Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection

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
  change `c.ofIsPullback sq`, a compactification of `f'`, the morphism
  `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` (in diagrammatic `⋙`-order), where
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
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`; the compactification `Z` of
`f.left` and `Z ×_Y Y'` are then so as well, as objects of `Over (Spec (.of k))`
(`Compactification.overObj` of `WeilConjectures.Compactification.Over`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`: the
  canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for a commutative square of open
  immersions, and its three steps; for a cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`:
  the morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` for a compactification `c`.
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
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

section OpenImmersion

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

/-- The cartesian extension-by-zero exchange has a left inverse.

Source: the proof of `thm-sfb-dc-open-base-change-iso` in the blueprint. On every
pro-étale object the inverse is induced by the identification of the two cartesian
pullback sections; the componentwise left-inverse equations assemble naturally.
(blueprint: stage3-sfb-open-base-change-left-inverse) -/
theorem boundedConstructibleOpenImmersionLowerShriekBaseChange_leftInverse
    (sq : IsPullback g' j' j g) :
    ∃ β : boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
        boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j',
      β ≫ boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq =
        𝟙 (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
          boundedConstructibleUpperStar Λ ℓ g) := by
  have hcomponent (K : Dᵇc(X.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq).app K) := by
    have := boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono Λ ℓ sq
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) rfl K
    obtain ⟨β, hβ⟩ := boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section Λ ℓ sq
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) rfl K
    have hγ :
        (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq).app K ≫
          β = 𝟙 _ := by
      apply (cancel_mono
        ((boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq).app K)).1
      simp only [Category.assoc, hβ, Category.comp_id, Category.id_comp]
    exact ⟨⟨β, hγ, hβ⟩⟩
  have := NatIso.isIso_of_isIso_app
    (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)
  exact ⟨inv (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq),
    IsIso.inv_hom_id _⟩

/-- The cartesian extension-by-zero exchange has a right inverse.

Source: the proof of `thm-sfb-dc-open-base-change-iso` in the blueprint. The same
cartesian section identification gives the opposite inverse equation, naturally.
(blueprint: stage3-sfb-open-base-change-right-inverse) -/
theorem boundedConstructibleOpenImmersionLowerShriekBaseChange_rightInverse
    (sq : IsPullback g' j' j g) :
    ∃ γ : boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
        boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j',
      boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq ≫ γ =
        𝟙 (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j') := by
  obtain ⟨β, hβ⟩ := boundedConstructibleOpenImmersionLowerShriekBaseChange_leftInverse Λ ℓ sq
  have hcomponent (K : Dᵇc(X.left)⟦Λ⟧) :
      Mono ((boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq).app K) :=
    boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono Λ ℓ sq
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) rfl K
  have := NatTrans.mono_of_mono_app
    (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)
  refine ⟨β, ?_⟩
  apply (cancel_mono
    (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)).1
  simp only [Category.assoc, hβ, Category.comp_id, Category.id_comp]

/-- **Base change for extension by zero** on bounded constructible complexes: for a *cartesian*
square with `j` and `j'` open immersions, the exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` is
an isomorphism.

Mathematically, since the square is cartesian, `X'` is the preimage of the open subscheme
`X ⊆ Z` under `g`, and on stalks at points of `Z'_proét` both sides are the pulled-back stalk at
points of `X'` and vanish outside `X'`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) := by
  obtain ⟨β, hβ⟩ := boundedConstructibleOpenImmersionLowerShriekBaseChange_leftInverse Λ ℓ sq
  obtain ⟨γ, hγ⟩ := boundedConstructibleOpenImmersionLowerShriekBaseChange_rightInverse Λ ℓ sq
  have hβγ : β = γ := by
    calc
      β = β ≫ 𝟙 _ := by simp
      _ = β ≫ (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq ≫ γ) := by
        rw [hγ]
      _ = (β ≫ boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq) ≫ γ := by
        rw [Category.assoc]
      _ = γ := by rw [hβ, Category.id_comp]
  exact ⟨⟨β, by rw [hβγ]; exact hγ, hβ⟩⟩

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

end OpenImmersion

/-! ### The compact-support base-change morphism for a compactification -/

section LowerShriek

variable [IsFinitenessCoefficient ℓ Λ] {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'`: with
`Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙
      boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI)
      (boundedConstructibleBaseChange Λ ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar Λ ℓ (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ ℓ c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI)
          (boundedConstructibleBaseChange Λ ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar Λ ℓ (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

end Compactification

/-! ### For the lower shriek -/

section Chosen

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `E`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into
`Rf'_!^{c_f.ofIsPullback sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

lemma boundedConstructibleLowerShriekBaseChange_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange ℓ E sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange]

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into
`Rf'_!^{c_f.ofIsPullback sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting _ ℓ
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl]

end Chosen

end AlgebraicGeometry.ProEtale.CondensedRing
