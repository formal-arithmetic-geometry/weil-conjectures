/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Composition of the derived lower and upper shrieks on bounded constructible complexes

As in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, all
schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`. For composable morphisms
`f : X ⟶ Y` and `g : Y ⟶ S`, this file gives, for the coefficient rings `E̲` of a finite extension
`E` of `ℚ_ℓ` and `ℚ̲̄_ℓ`, the composition isomorphisms
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
The *exchange isomorphism* `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*` of the cartesian square is
`boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`, an isomorphism for `p'` proper
(`isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`).

## The upper shriek

The second isomorphism is the conjugate (`conjugateIsoEquiv`) of the first under the
adjunctions `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, the latter being the
composite of `Rf_! ⊣ Rf^!` and `Rg_! ⊣ Rg^!`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` and its `_padicAlgCl` version:
  `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for `E`- and `ℚ̄_ℓ`-sheaves.
- `ProEtale.CondensedRing.boundedConstructibleUpperShriekComp` and its `_padicAlgCl` version:
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for `E`- and `ℚ̄_ℓ`-sheaves.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `E`-sheaves: for the chosen compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of
`f` and `c' = (Y ⟶[j] Z' ⟶[q] S)` of `g`, and a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')` of
`p ≫ j` with cartesian square (`Compactification.exists_isPullback_overG_overI`), the composite
of the independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso`) for the composite compactification
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S`, of the composition isomorphisms of `j_!` and `Rf_*`, and of the
inverse of the exchange isomorphism `Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ g :=
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
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ E hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso ℓ E _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        _ ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `ℚ̄_ℓ`-sheaves, constructed as
`boundedConstructibleLowerShriekComp`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_padicAlgCl :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ g :=
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
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        _ ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `E`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp :
    boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ g ⋙
        boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction _ ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction _ ℓ g))
    (boundedConstructibleLowerShriekComp ℓ E f g).symm

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` for the exceptional inverse image on
bounded constructible `ℚ̄_ℓ`-sheaves: the conjugate of
`boundedConstructibleLowerShriekComp_padicAlgCl` under the adjunctions
`R(f ≫ g)_! ⊣ R(f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekComp_padicAlgCl :
    boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫ g) ≅
      boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ (f ≫ g))
    ((boundedConstructibleUpperShriekAdjunction _ ℓ f).comp
      (boundedConstructibleUpperShriekAdjunction _ ℓ g))
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).symm

end AlgebraicGeometry.ProEtale.CondensedRing
