/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationLowerStarBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.Compactification.NagataCompactification

/-!
# Separated direct images commute with generic base change

Let `S` be an integral scheme of finite type over a field `k`, let `Λ` be a finite ring whose
exponent is invertible on `S`, and let `t : T ⟶ S` be a morphism from a noetherian scheme `T`
lying over the generic point of `S`. For a separated morphism `h : X ⟶ Y` of finite type, with
`Y` of finite type over `S`, and its base change `h_T : X_T ⟶ Y_T` along `g : Y_T ⟶ Y`, the
derived base change map

`Ex_* : g^* Rh_* L ⟶ Rh_{T,*} g'^* L`

is an isomorphism for every bounded constructible `L` on `X`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_generic`).

## Implementation details

A Nagata compactification `h = p ∘ j`, with `j` an open immersion and `p` proper, base changes
to a compactification of `h_T`, and the base change map of `h` is the pasting of those of `j`
and `p` (`AlgebraicGeometry.Etale.map_rightDerivedLowerStarCompHom_derivedBaseChangeMap`). The one
of `p` is invertible by proper base change, the one of `j` by the open immersion case
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Direct images commute with generic base change.** Let `S` be integral and of finite type
over a field `k`, let `Λ` be a finite ring whose exponent is invertible on `S`, and let
`t : T ⟶ S` be a morphism from a noetherian scheme lying over the generic point of `S`. For a
separated morphism of finite type `h : X ⟶ Y`, with `Y` of finite type over `S`, and base changes
`g : Y_T ⟶ Y`, `g' : X_T ⟶ X`, `h_T : X_T ⟶ Y_T`, the derived base change map
`g^* Rh_* L ⟶ Rh_{T,*} g'^* L` is an isomorphism for every bounded constructible complex `L`
on `X`. -/
theorem isIso_derivedBaseChangeMap_app_of_generic {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] {T : Scheme.{u}} [IsNoetherian T] (t : T ⟶ S)
    (ht : ∀ x, t.base x = genericPoint S) {X Y XT YT : Scheme.{u}} (fY : Y ⟶ S)
    [LocallyOfFiniteType fY] [QuasiCompact fY] (h : X ⟶ Y) [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h] {g : YT ⟶ Y} {fT : YT ⟶ T}
    (hY : IsPullback g fT fY t) {g' : XT ⟶ X} {hT : XT ⟶ YT} (sq : IsPullback g' hT h g)
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (fY ≫ aS)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  let c := NagataCompactification h
  have hp : IsPullback (pullback.fst c.g g) (pullback.snd c.g g) c.g g := .of_hasPullback _ _
  have hi : IsPullback g' (pullback.lift (g' ≫ c.i) hT (by rw [Category.assoc, ← c.comm,
      sq.w])) c.i (pullback.fst c.g g) :=
    IsPullback.of_bot (by rw [pullback.lift_snd, ← c.comm]; exact sq)
      (pullback.lift_fst _ _ _).symm hp
  let c' : Compactification hT :=
    { Z := pullback c.g g
      g := pullback.snd c.g g
      i := pullback.lift (g' ≫ c.i) hT (by rw [Category.assoc, ← c.comm, sq.w])
      comm := (pullback.lift_snd _ _ _).symm
      isProper := MorphismProperty.of_isPullback hp inferInstance
      isOpenImmersion := MorphismProperty.of_isPullback hi inferInstance }
  have : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) hp.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite hp
  have hYZ : IsPullback (pullback.fst c.g g) (pullback.snd c.g g ≫ fT) (c.g ≫ fY) t :=
    hp.paste_vert hY
  have : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) hi.toCommSq).app L) :=
    isIso_derivedBaseChangeMap_app_of_isOpenImmersion_of_generic Λ aS t ht (c.g ≫ fY) c.i hYZ
      hi hL
  have key := map_rightDerivedLowerStarCompHom_derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    sq.toCommSq c c' _ hi hp.toCommSq L
  have : IsIso (L((g)^*[ModuleCat.{u + 1} Λ]).map
      ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) c.i c.g h c.comm).app L) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left (L((g)^*[ModuleCat.{u + 1} Λ]).map
    ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) c.i c.g h c.comm).app L)) _

end Etale

end AlgebraicGeometry
