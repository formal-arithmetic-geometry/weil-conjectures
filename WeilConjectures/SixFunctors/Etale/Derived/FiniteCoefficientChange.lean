/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChangeRingEquiv
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Stability

/-!
# Finite coefficient change for the ordinary direct image

Let `Λ` be a finite ring (the coefficient stage `A = A_{E,n}`) and `B = Λ ⧸ J` a quotient of it
(for instance `A_{E,m}`, `m ≤ n`). For `f : X ⟶ Y` a morphism of finite type `k`-schemes and
`K ∈ Dctf(X, Λ)` with derived base change `K_B ∈ D(X_ét, B)`, the direct image commutes with the
coefficient change: `(Rf_{*,Λ} K) ⊗ᴸ_Λ B ≅ Rf_{*,B}(K_B)`, the right hand side being read in
`D(Y_ét, Λ)` after restriction of scalars (blueprint `lem-coef-finite-direct-image`).

The proof follows the blueprint:

* direct image computed with `B`-coefficients has the same underlying `Λ`-module object:
  restriction of scalars commutes with the derived direct image on bounded below objects
  (`AlgebraicGeometry.Etale.nonempty_iso_derivedRestrictScalars_rightDerivedLowerStar`, from
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`);
* the restriction of scalars of `K_B` is the reduction `K ⊗ᴸ B_X`
  (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_of_isDerivedBaseChange`);
* the projection formula with the finite constant coefficient `B`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`,
  blueprint `lem-sf-projection-finite-constant`) identifies `Rf_*(K ⊗ᴸ B_X)` with
  `Rf_* K ⊗ᴸ B_Y`.

## Implementation notes

As elsewhere in the repository
(`WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`), the comparison is only
asserted to exist; its naturality, its compatibility with composition and successive quotients,
and the transport to the pro-étale realization are not formalised.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is locally small. Instance search does not find this in the
presence of the imports of this file. -/
local instance (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- **Restriction of scalars commutes with the derived direct image** on bounded below
objects: for `M ∈ D⁺(X_ét, Λ')`, `Res(Rf_* M) ≅ Rf_*(Res M)`. This is the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerStarRestrictScalars` on `D⁺`, transported to the
unbounded derived categories. -/
theorem nonempty_iso_derivedRestrictScalars_rightDerivedLowerStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : 𝐃(X, Λ')) (n : ℤ) [M.IsGE n] :
    Nonempty ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj M) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M)) := by
  let M' : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :=
    ⟨M, ⟨n, inferInstance⟩⟩
  let RX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let RY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  exact ⟨RY.mapDerivedCategory.mapIso
      (((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusCompatibility.symm.app M') ≪≫
    (RY.mapDerivedCategoryPlusCompatibility.symm.app _) ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      (asIso ((rightDerivedLowerStarRestrictScalars φ f).app M')) ≪≫
    ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
      (RX.mapDerivedCategoryPlus.obj M') ≪≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso (RX.mapDerivedCategoryPlusCompatibility.app M')⟩

end RestrictScalars

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (J : Ideal Λ) {k : Type u} [Field k]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
  (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hf hd in
/-- Blueprint `lem-coef-finite-direct-image`: Finite coefficient change for ordinary direct
image.

Let `Λ` be a finite ring, `B = Λ ⧸ J`, and `f : X ⟶ Y` a morphism of finite type `k`-schemes
with `dim X ≤ d`. For `K ∈ Dctf(X, Λ)` and a derived base change `η : K ⟶ Res K_B` of `K` to
`D(X_ét, B)` (`CategoryTheory.Sheaf.IsDerivedBaseChange`), the coefficient change commutes with
the direct image: `(Rf_{*,Λ} K) ⊗ᴸ_Λ B ≅ Rf_{*,B}(K_B)` in `D(Y_ét, Λ)`, the left hand side being
the reduction `AlgebraicGeometry.Etale.reductionModIdeal` and the right hand side read after
restriction of scalars. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerStar_of_constructibleFiniteTor
    {K : 𝐃(X, Λ)} (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    {KB : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj KB}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk J)).obj
        ((R((f)_*[ModuleCat.{u + 1} (Λ ⧸ J)])).obj KB) ≅
      (reductionModIdeal Λ Y J).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨-, a, b, hta⟩ := hK
  have : K.IsLE b := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta).2
  let B := ModuleCat.of Λ (Λ ⧸ J)
  obtain ⟨eB⟩ := nonempty_iso_reductionModIdeal_of_isDerivedBaseChange hη
  obtain ⟨h₁, -⟩ := (torAmplitudeIn_iff_forall_derivedTensor _ X a b K).1 hta
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj B)
  have : ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj
      KB).IsGE a :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso eB.symm a
  have := Sheaf.isGE_of_isGE_derivedRestrictScalars_obj (Ideal.Quotient.mk J) KB a
  obtain ⟨e₁⟩ := nonempty_iso_derivedRestrictScalars_rightDerivedLowerStar
    (Ideal.Quotient.mk J) f KB a
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ aX aY f hf d hd K b B
  exact ⟨e₁ ≪≫ (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso eB ≪≫
    ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f B))).symm ≪≫
    (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y B))).symm⟩

end Etale

end AlgebraicGeometry
