/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange

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

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`:
  the morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` for a compactification `c`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`: the morphism
  `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for `E`- and `ℚ̄_ℓ`-sheaves.

The extension-by-zero exchange morphism and its inverse
`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso` are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`.

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

/-! ### The compact-support base-change morphism for a compactification -/

section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
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
