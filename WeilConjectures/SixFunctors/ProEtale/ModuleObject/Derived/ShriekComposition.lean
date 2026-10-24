/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-!

# Composition of the derived lower and upper shrieks on bounded constructible complexes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all
schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`. For composable morphisms
`f : X ⟶ Y` and `g : Y ⟶ S`, this file gives, for the coefficient ring `ℚ̲̄_ℓ`, the composition
isomorphisms
```
R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!,      R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!
```
on the bounded constructible derived categories.

## The lower shriek

The lower shriek `Rf_!` is defined through the compactification `compactificationOverField f`
chosen for each morphism separately, so the first isomorphism compares three unrelated
compactifications. Write `c = (X ⟶[i] Z ⟶[p] Y)` and `c' = (Y ⟶[j] Z' ⟶[q] S)` for the chosen
compactifications of `f` and `g`, and choose a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of
`p ≫ j` whose square
```
Z --i'--> W
|p        |p'
v         v
Y --j---> Z'
```
is cartesian (`Compactification.exists_isPullback_overG_overI`). Then
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` is a compactification of `f ≫ g` (`Compactification.overComp`), and
```
R(f ≫ g)_! ≅ (i ≫ i')_! ⋙ R(p' ≫ q)_*          (independence of the compactification)
           ≅ i_! ⋙ (i'_! ⋙ Rp'_*) ⋙ Rq_*      (composition of `j_!` and of `Rf_*`)
           ≅ i_! ⋙ (Rp_* ⋙ j_!) ⋙ Rq_*        (the exchange isomorphism)
           = Rf_! ⋙ Rg_!.
```
The *exchange morphism* `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of the cartesian square
(`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`) is the mate, under the
adjunctions `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism
`j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`). It is an isomorphism for `p'`
proper.

## The upper shriek

The second isomorphism is the conjugate (`conjugateIsoEquiv`) of the first under the
adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, the latter being the
composite of `Rf_! ⊣ Rf^!` and `Rg_! ⊣ Rg^!`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`: the
  exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*`.
- `boundedConstructibleLowerShriekComp_padicAlgCl`:
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
- `boundedConstructibleUpperShriekComp_padicAlgCl`:
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`.

## Sorried input

- `isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl`:
  the exchange morphism is an isomorphism for `p'` proper.
- `Compactification.exists_isPullback_overG_overI`: the existence of the compactification `d`.

-/

@[expose] public section

universe u

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

/-- The *unit insertion* step of the exchange morphism: the natural transformation
`Rp_* ⋙ j_! ⟶ (Rp_* ⋙ j_!) ⋙ (Lp'^* ⋙ Rp'_*)` obtained by inserting the unit of the adjunction
`Lp'^* ⊣ Rp'_*`. -/
noncomputable def boundedConstructibleLowerStarOpenImmersionLowerShriekExchangeUnitStep :
    boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ j ⟶
      (boundedConstructibleLowerStar ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj ℓ) ℓ j) ⋙
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p' ⋙
          boundedConstructibleLowerStar ℓ p') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ p').unit

/-- The *square transport* step of the exchange morphism: `Functor.squareTransport` applied to
the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!` of the cartesian
square, under `Rp_*` on the left and `Rp'_*` on the right. -/
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

/-- The *counit contraction* step of the exchange morphism: the natural transformation
`(Rp_* ⋙ Lp^*) ⋙ (i'_! ⋙ Rp'_*) ⟶ i'_! ⋙ Rp'_*` obtained by contracting the counit of the
adjunction `Lp^* ⊣ Rp_*`. -/
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
with `j` and `i'` open immersions: the mate, under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`, of the extension-by-zero base-change isomorphism `j_! ⋙ Lp'^* ≅ Lp^* ⋙ i'_!`
(`boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`), assembled as the composite of the
unit insertion, the square transport, and the counit contraction:
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

end Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

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
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ sq) :=
  sorry

end ExchangeIsIso

/-! ### The composition isomorphisms -/

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `ℚ̄_ℓ`-sheaves: for the chosen compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of
`f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of
`p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the composite
of the independence of the compactification
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

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `ℚ̄_ℓ`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp_padicAlgCl` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_padicAlgCl :
    boundedConstructibleUpperShriek ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek ℓ g ⋙
        boundedConstructibleUpperShriek ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction ℓ g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).symm

end AlgebraicGeometry.ProEtale.CondensedRing
