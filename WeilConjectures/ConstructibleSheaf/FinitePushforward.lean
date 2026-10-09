/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Presentable.Finite
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Constructible sheaves embed into finite pushforwards of constant sheaves

Let `U` be a quasi-compact and quasi-separated scheme and `C` a constructible sheaf of
`Λ`-modules on the small étale site of `U`, for a noetherian ring `Λ`. Then `C` embeds into a
finite direct sum `⨁ᵢ (hᵢ)_* Mᵢ` of pushforwards of constant sheaves with finitely generated
values `Mᵢ` along finite and finitely presented morphisms `hᵢ : Vᵢ ⟶ U` [Stacks 09Z7]. This is
the input to Gabber's effacement argument (`WeilConjectures.SixFunctors.Etale.Gabber`).

The proof goes through Noetherian approximation: the case of a Noetherian base [Stacks 09Z6]
uses that constructible sheaves are finitely presented objects of the category of sheaves
[Stacks 09Z4] and that the constant sheaf on a normal integral scheme is the pushforward of
its restriction to the generic point [Stacks 09Z5]; the general case descends `C` to a
Noetherian scheme and pulls the embedding back along the finite base change isomorphism
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`.

The bounded constructible complexes of the blueprint (`def-weil-pbc-constructible-complexes`)
are `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` of
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed`: on a normal
  integral scheme the constant sheaf is the pushforward of its restriction to the generic
  point, or to a nonempty open subscheme.
- `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf`: constructible
  sheaves are finitely presentable.
- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`: the embedding
  over a Noetherian base.
- `AlgebraicGeometry.Etale.exists_isNoetherian_mono_biproduct_lowerStar`: Noetherian
  approximation of the embedding.
- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar`: the embedding over a
  quasi-compact quasi-separated base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Étale sheaves of `Λ`-modules have finite biproducts (an abelian category has them; stated
explicitly since instance search times out on the general route). -/
noncomputable instance Etale.hasFiniteBiproducts_sheaf_moduleCat (X : Scheme.{u}) :
    HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **Constant sheaves on a normal scheme.** Let `Y` be an integral scheme all of whose local
rings are integrally closed, `g : Spec K ⟶ Y` the inclusion of its generic point and `M` a
`Λ`-module. Then the unit `M_Y ⟶ g_* g^* M_Y = g_* M_{Spec K}` is an isomorphism; the same
holds for the inclusion of a nonempty open subscheme.

The blueprint states this for a finite abelian group `E`; the proof (the strict henselisation
of a normal local ring is a normal domain, so the generic fibre of `Spec 𝒪ˢʰ_{Y,ȳ}` is
irreducible) applies to an arbitrary value `M`.
(blueprint: `lem-weil-pbc-normal-constant-generic`) -/
@[stacks 09Z5]
theorem Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
      ∀ {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U],
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  sorry

/-- **Constructible sheaves are finitely presentable.** On a quasi-compact quasi-separated
scheme `X`, with `Λ` Noetherian, a constructible sheaf of `Λ`-modules `F` is a finitely
presentable object of the category of sheaves: `Hom(F, -)` commutes with filtered colimits
(indexed by small categories), i.e. every morphism from `F` to a filtered colimit factors
through a stage, and two such factorisations agree at a later stage.
(blueprint: `lem-weil-pbc-constructible-finitely-presented`) -/
@[stacks 09Z4]
theorem Etale.isFinitelyPresentable_of_isConstructibleSheaf [IsNoetherianRing Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsFinitelyPresentable.{u} F :=
  sorry

/-- **The finite-pushforward embedding over a Noetherian base.** A constructible sheaf of
`Λ`-modules `C` on a Noetherian scheme `U` admits a monomorphism
`C ⟶ ⨁ᵢ (hᵢ)_* Mᵢ` into a finite direct sum of pushforwards of constant sheaves with finitely
generated values `Mᵢ` along finite morphisms `hᵢ : Vᵢ ⟶ U`, for `Λ` noetherian.
(blueprint: `lem-weil-pbc-constructible-finite-pushforward-noetherian`) -/
@[stacks 09Z6]
theorem Etale.exists_mono_biproduct_lowerStar_of_isNoetherian [IsNoetherianRing Λ]
    {U : Scheme.{u}} [IsNoetherian U]
    (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C] :
    ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U) (_ : ∀ i, IsFinite (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
      (φ : C ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ :=
  sorry

section Auxiliary

/-! ### Auxiliary lemmas -/

/-- **Descent of a constructible sheaf to a Noetherian scheme.** A constructible sheaf of
`Λ`-modules on a quasi-compact quasi-separated scheme `U`, for `Λ` noetherian, is the pullback
of a constructible sheaf on a Noetherian scheme `U'` along some morphism `U ⟶ U'`: its strata
are constructible and its finitely generated stalks finitely presented, so write `U` as a
cofiltered limit of schemes of finite type over `ℤ` with affine transition maps [Stacks 01ZA] and
descend the finitely many étale objects, sections and relations presenting `C` to one stage.
This is Step 2 of `lem-weil-pbc-constructible-finite-pushforward-approximation`. -/
theorem Etale.exists_isNoetherian_upperStar_iso [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) :=
  sorry

/-- **Pulling back a finite-pushforward embedding.** If `C'` on `U'` embeds into a finite sum
of pushforwards of constant sheaves along finite, finitely presented morphisms, then so does
its pullback along any `ν : U ⟶ U'`: pullback is exact, commutes with finite sums, and with
pushforward along finite morphisms (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`),
and it preserves constant sheaves. -/
theorem Etale.exists_mono_biproduct_lowerStar_upperStar {U U' : Scheme.{u}} (ν : U ⟶ U')
    (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {r : ℕ} (V : Fin r → Scheme.{u})
    (h : ∀ i, V i ⟶ U') [∀ i, IsFinite (h i)] [∀ i, LocallyOfFinitePresentation (h i)]
    (M : Fin r → ModuleCat.{u + 1} Λ)
    (φ : C' ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
      ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) [Mono φ] :
    ∃ (V' : Fin r → Scheme.{u}) (h' : ∀ i, V' i ⟶ U) (_ : ∀ i, IsFinite (h' i))
      (_ : ∀ i, LocallyOfFinitePresentation (h' i))
      (φ' : ((ν)^*[_]).obj C' ⟶ ⨁ fun i ↦ ((h' i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V' i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ' := by
  let sq (i : Fin r) := IsPullback.of_hasPullback (h i) ν
  have (i : Fin r) := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) (sq i)
  let e (i : Fin r) := asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (sq i).toCommSq).app
    ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) ≪≫
      ((pullback.snd (h i) ν)_*[ModuleCat.{u + 1} Λ]).mapIso
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst (h i) ν)).app (M i))
  refine ⟨fun i ↦ pullback (h i) ν, fun i ↦ pullback.snd (h i) ν, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, ((ν)^*[_]).map φ ≫ (((ν)^*[_]).mapBiproduct _).hom ≫
      (biproduct.mapIso e).hom, inferInstance⟩

end Auxiliary

/-- **Noetherian approximation of the finite-pushforward embedding.** A constructible sheaf
of `Λ`-modules `C` on a quasi-compact quasi-separated scheme `U` is the pullback
`ν^* C' ≅ C` of a constructible sheaf `C'` on a Noetherian scheme `U'` along a morphism
`ν : U ⟶ U'`, and `C'` admits a monomorphism into a finite direct sum of pushforwards of
constant sheaves with finitely generated values along finite, finitely presented morphisms.

The blueprint takes `U'` to be a stage `U_λ` of an inverse system `U = lim U_λ` of Noetherian
schemes with affine transition maps; only the stage is used afterwards, so the inverse system
is not recorded. That the pullback of the embedding is an embedding of `C` is
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar`.
(blueprint: `lem-weil-pbc-constructible-finite-pushforward-approximation`) -/
theorem Etale.exists_isNoetherian_mono_biproduct_lowerStar [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) ∧
      ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U') (_ : ∀ i, IsFinite (h i))
        (_ : ∀ i, LocallyOfFinitePresentation (h i))
        (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
        (φ : C' ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
          ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  obtain ⟨U', ν, C', hU', hC', e⟩ := Etale.exists_isNoetherian_upperStar_iso Λ C
  obtain ⟨r, V, h, hh, M, hM, φ, hφ⟩ := Etale.exists_mono_biproduct_lowerStar_of_isNoetherian Λ C'
  exact ⟨U', ν, C', hU', hC', e, r, V, h, hh, fun _ ↦ inferInstance, M, hM, φ, hφ⟩

/-- **Constructible sheaves embed into finite pushforwards.** A constructible sheaf of
`Λ`-modules `C` on a quasi-compact quasi-separated scheme `U` admits a monomorphism
`C ⟶ ⨁ᵢ (hᵢ)_* Mᵢ` into a finite direct sum of pushforwards of constant sheaves with finitely
generated values `Mᵢ` along finite and finitely presented morphisms `hᵢ : Vᵢ ⟶ U`, for `Λ`
noetherian. The blueprint states this for torsion sheaves, over a finite ring `Λ`, where the
`Mᵢ` are finite.
(blueprint: `lemma-weil-pbc-constructible-finite-pushforward`) -/
@[stacks 09Z7]
theorem Etale.exists_mono_biproduct_lowerStar [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U) (_ : ∀ i, IsFinite (h i))
      (_ : ∀ i, LocallyOfFinitePresentation (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
      (φ : C ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  obtain ⟨U', ν, C', -, -, ⟨e⟩, r, V, h, hh, hfp, M, hM, φ, hφ⟩ :=
    Etale.exists_isNoetherian_mono_biproduct_lowerStar Λ C
  obtain ⟨V', h', hh', hfp', φ', hφ'⟩ :=
    Etale.exists_mono_biproduct_lowerStar_upperStar Λ ν C' V h M φ
  exact ⟨r, V', h', hh', hfp', M, hM, e.inv ≫ φ', inferInstance⟩

end AlgebraicGeometry
