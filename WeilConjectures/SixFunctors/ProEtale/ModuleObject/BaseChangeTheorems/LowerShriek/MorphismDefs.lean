/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange

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
The extension-by-zero exchange is stated for a general `Λ`; the morphisms involving the
pushforward are defined for each of the `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (in
the namespaces `ProEtale.CondensedRing`, `ProEtale.CondensedRing.ContinuousMapRingObj` and
`ProEtale.CondensedRing.PadicIntegersRingObj`).

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
    base change for extension by zero asserts that it is an isomorphism
    (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`),
    and the pasting uses its inverse.
* **For the lower shriek.** For the coefficient rings `E̲` of a finite subextension `E ⊆ ℚ̄_ℓ` and
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

## Main results

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`: base
  change for extension by zero. The morphism is the exchange morphism
  `boundedConstructibleOpenImmersionLowerShriekBaseChange'` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`, which is
  an isomorphism by `isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'` (blueprint
  `sk-def-sfb-open-base-change`).

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
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`ℚ̄_ℓ`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar ℓ (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar ℓ (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`E`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ E (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.continuousMapRingObj E) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.continuousMapRingObj E)
        ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`E`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.continuousMapRingObj E) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.continuousMapRingObj E)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom :=
  by delta boundedConstructibleLowerShriekOfCompactificationBaseChangePasting; rfl

end LowerShriek

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`𝒪_E`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ E (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
        (Profinite.padicIntegersRingObj ℓ E) ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStar ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`𝒪_E`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E c sq =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.padicIntegersRingObj ℓ E)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStar ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

end PadicIntegersRingObj

end Compactification

/-! ### For the lower shriek -/

section Chosen

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `E`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
into `Rf'_!^{c_f.ofIsPullback sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f' :=
  ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

/-- The defining equation of `boundedConstructibleLowerShriekBaseChange` (`E`-coefficient). -/
lemma boundedConstructibleLowerShriekBaseChange_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange ℓ E sq =
      ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange]

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism
`boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into `Rf'_!^{c_f.ofIsPullback
sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek ℓ f ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriek ℓ f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

/-- The defining equation of `boundedConstructibleLowerShriekBaseChange_padicAlgCl`
(`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl]

end Chosen

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Composition of the derived lower shriek on bounded constructible `ℚ̄_ℓ`-complexes

The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square of an open immersion and
a proper morphism, and, for the coefficient ring `ℚ̲̄_ℓ`, the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. The construction is explained in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`, which also treats
the coefficient rings `E̲` and the upper shriek.
## Main definitions
- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the
  exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`:
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
-/

open scoped CategoryTheory.Obj

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

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

/-- The *unit insertion* step of the exchange morphism (`ℚ̄_ℓ`-coefficient): the natural
transformation `Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the
adjunction `Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ p').unit

/-- The *square transport* step of the exchange morphism (`ℚ̄_ℓ`-coefficient):
`Functor.squareTransport` applied to the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅
Lp^* ⋙ i'_!` of the cartesian square, under `Rp_*` on the left and `Rp'_*` on the right. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    (sq : IsPullback p i' j p') :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ p') ≅
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar
        (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  Functor.squareTransport (boundedConstructibleLowerStar ℓ p)
    (boundedConstructibleLowerStar ℓ p')
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ sq)

/-- The *counit contraction* step of the exchange morphism (`ℚ̄_ℓ`-coefficient): the natural
transformation `(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of
the adjunction `Lp^* ⊣ Rp_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep :
    (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
          boundedConstructibleLowerStar ℓ p') ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).counit _ ≫
    (Functor.leftUnitor _).hom

/-- The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` on bounded constructible complexes for
a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions (`ℚ̄_ℓ`-coefficient): the mate, under the adjunctions `Lp^* ⊣
Rp_*` and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙
i'_!` (`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of
the unit insertion, the square transport, and the counit contraction:
`Rp_* ⋙ j_! ⟶ Rp_* ⋙ j_! ⋙ Lp'^* ⋙ Rp'_* ≅ Rp_* ⋙ Lp^* ⋙ i'_! ⋙ Rp'_* ⟶ i'_! ⋙ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i' ⋙
        boundedConstructibleLowerStar ℓ p' :=
  boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep ℓ ≫
    (boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep ℓ sq).hom ≫
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeCounitStep ℓ

/-- The exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` is the exchange morphism
`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`: the two
extension-by-zero base-change morphisms they are built from are the same exchange morphism. -/
lemma boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq
    (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq =
      boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ sq := by
  have e : boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
      (Profinite.padicAlgClRingObj ℓ) ℓ sq =
      boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
        (Profinite.padicAlgClRingObj ℓ) ℓ sq := by
    refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
    change boundedConstructibleOpenImmersionLowerShriekBaseChange
        (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq =
      boundedConstructibleOpenImmersionLowerShriekBaseChange'
        (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq
    rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
      boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
  unfold boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeSquareStep'
  rw [e]
  rfl

end Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExchangeIsIso

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq) := by
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq]
  exact isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ sq

end ExchangeIsIso

/-! ### The composition isomorphisms -/

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `ℚ̄_ℓ`-sheaves: for the chosen compactifications `c = (X
⟶[i] Z ⟶[p] Y)` of `f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W
⟶[p'] Z')` of `p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the
composite of the independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`) for the composite
compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!`
and `Rf_*`, and of the inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_padicAlgCl :
    boundedConstructibleLowerShriek ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleLowerShriek ℓ g :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The isomorphism `R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` attached to compactifications `c` of `f` and
`c'` of `g` and a compactification `d` of `p ≫ j` with cartesian square `hd`, as in the definition
of `boundedConstructibleLowerShriekComp_padicAlgCl`. -/
noncomputable def boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl
    (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left)
    (hd : IsPullback c.overG d.overI c'.overI d.overG) :
    boundedConstructibleLowerShriek ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c' :=
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper (Compactification.overCompObjIso c c' d).hom.left := by
    simp only [Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ hd
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        ℓ hd)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism of the lower shriek is the isomorphism attached to the chosen
compactifications. -/
lemma boundedConstructibleLowerShriekComp_padicAlgCl_eq :
    boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g =
      boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g
        (compactificationOverField f) (compactificationOverField g)
        (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
          (compactificationOverField g)).choose
        (Compactification.exists_isPullback_overG_overI (compactificationOverField f)
          (compactificationOverField g)).choose_spec := by
  unfold boundedConstructibleLowerShriekComp_padicAlgCl
    boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
