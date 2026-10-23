/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

/-!

# Coefficients and geometric categories

This file formalises the coefficient setup of the trace formula (blueprint `sk-d-setup`): the
subcategories `Dᵇctf(X, A) ⊂ D(X_proét, A)` of bounded constructible complexes of finite Tor
amplitude are triangulated, closed under isomorphisms, stable under `Lf^*` for every morphism
`f` and under `Rf_!` for every compactifiable morphism `f`.

The blueprint fixes `A = 𝒪_E/ϖ_Eⁿ` for a finite extension `E/ℚ_ℓ` and `ℓ` invertible on the base
field `k`. Here `A` is generalised to an arbitrary finite commutative ring `Λ` whose exponent is
invertible on `k` (`AlgebraicGeometry.HasInvertibleExponent`).

## Main definitions

- `AlgebraicGeometry.ProEtale.IsCoefficientSetup`: the properties required of a family of
  subcategories `P X ⊂ D(X_proét, Λ)` in the blueprint.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_finiteTorAmplitude`: finite Tor
  amplitude is a triangulated property of objects of `D(X_proét)`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_constructibleFiniteTor`:
  `Dᵇctf(X, Λ)` is a triangulated subcategory of `D(X_proét, Λ)`.
- `AlgebraicGeometry.ProEtale.isCoefficientSetup_constructibleFiniteTor`: the family
  `X ↦ Dᵇctf(X, Λ)` satisfies `IsCoefficientSetup`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section FiniteTorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- Finite Tor amplitude is a triangulated property of objects of `D(X_proét)`: the derived
tensor product `- ⊗ᴸ F` is a triangulated functor, and concentration in an interval is stable
under shifts and under extensions, with the interval shifted and widened. -/
instance DerivedCategory.isTriangulated_finiteTorAmplitude :
    (DerivedCategory.finiteTorAmplitude A X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, 0, 0, fun F ↦ by
    have h : IsZero ((0 : _root_.DerivedCategory (Sheaf (ProEt.topology X) A)) ⊗
        (_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
      Functor.map_isZero
        ((curriedTensor (_root_.DerivedCategory (Sheaf (ProEt.topology X) A))).flip.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) (isZero_zero _)
    exact ⟨(_root_.DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h,
      (_root_.DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h⟩⟩
  isStableUnderShiftBy n := ⟨fun M ⟨a, b, h⟩ ↦ ⟨a - n, b - n, fun F ↦ by
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F)
    obtain ⟨h₁, h₂⟩ := h F
    let e := (((curriedTensor (_root_.DerivedCategory (Sheaf (ProEt.topology X) A))).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).commShiftIso n).app M
    have hge := _root_.DerivedCategory.TStructure.t.isGE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F) a n (a - n)
    have hle := _root_.DerivedCategory.TStructure.t.isLE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F) b n (b - n)
    exact ⟨@Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (a - n) hge,
      @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (b - n) hle⟩⟩⟩
  ext₂' T hT := by
    rintro ⟨a, b, h₁⟩ ⟨c, d, h₃⟩
    refine ObjectProperty.le_isoClosure _ _ ⟨min a c, max b d, fun F ↦ ?_⟩
    let G := (curriedTensor (_root_.DerivedCategory (Sheaf (ProEt.topology X) A))).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

end FiniteTorAmplitude

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `Dᵇctf(X, Λ)` is a triangulated subcategory of `D(X_proét, Λ)`, for a finite ring `Λ`. -/
instance DerivedCategory.isTriangulated_constructibleFiniteTor [Finite Λ] (X : Scheme.{u}) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
  inferInstanceAs (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X).IsTriangulated

/-- Blueprint `sk-d-setup`: the coefficient data of the trace formula.

A family `P X ⊂ D(X_proét, Λ)` of subcategories, indexed by all schemes `X`, is a *coefficient
setup* over the field `k` if every `P X` is a triangulated subcategory of `D(X_proét, Λ)`,
closed under isomorphisms, the family is stable under `Lf^*` for every morphism `f`, and stable
under `Rf_!` for every compactifiable quasi-compact morphism `f : X ⟶ Y` whose target `Y` is
locally of finite type and quasi-compact over `Spec k`.

The blueprint takes `Λ = 𝒪_E/ϖ_Eⁿ`; this predicate makes sense for any coefficient ring, and
`AlgebraicGeometry.ProEtale.isCoefficientSetup_constructibleFiniteTor` proves it for
`P = Dᵇctf(-, Λ)` with `Λ` finite of exponent invertible on `k`. -/
structure IsCoefficientSetup (k : Type u) [Field k]
    (P : ∀ X : Scheme.{u},
      ObjectProperty (_root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))) :
    Prop where
  /-- Each `P X` is a triangulated subcategory of `D(X_proét, Λ)`. -/
  isTriangulated (X : Scheme.{u}) : (P X).IsTriangulated
  /-- Each `P X` is closed under isomorphisms. -/
  isClosedUnderIsomorphisms (X : Scheme.{u}) : (P X).IsClosedUnderIsomorphisms
  /-- Stability under the derived pullback `Lg^*` along any morphism `g`. -/
  leftDerivedFunctor_upperStar_obj {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hK : P X K) :
    P Y (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)
  /-- Stability under the compact-support direct image `Rf_!` along a compactifiable
  morphism `f` over a finite-type `k`-scheme. -/
  rightDerivedLowerShriek_obj {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hK : P X K) :
    P Y ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K)

/-- Blueprint `sk-d-setup`: the subcategories `Dᵇctf(X, Λ)` of bounded constructible complexes
of finite Tor amplitude form a coefficient setup over `k`, for a finite commutative ring `Λ`
whose exponent is invertible on `k`. This generalises the blueprint's `A = 𝒪_E/ϖ_Eⁿ` with `ℓ`
invertible in `k`. -/
theorem isCoefficientSetup_constructibleFiniteTor [Finite Λ] (k : Type u) [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    IsCoefficientSetup Λ k fun X ↦ DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
    where
  isTriangulated _ := inferInstance
  isClosedUnderIsomorphisms _ := inferInstance
  leftDerivedFunctor_upperStar_obj g _ hK :=
    constructibleFiniteTor_leftDerivedFunctor_upperStar_obj g hK
  rightDerivedLowerShriek_obj aY _ _ f _ _ _ hK :=
    have : HasInvertibleExponent Λ _ := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK

end AlgebraicGeometry.ProEtale
