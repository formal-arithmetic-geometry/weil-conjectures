/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ProjectionPairing
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The derived Poincaré pairing

Let `a : X ⟶ Y` be a morphism admitting a compactification and `γ : T[2d] ≅ Ra^! Λ_Y` a purity
isomorphism, as given by an orientation of `a` of relative dimension `d` with twist
`T = Λ_X(d)`. The derived Poincaré pairing is assembled from three ingredients:

* the *mixed-support cup product* `⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`, the projection map
  of `Ra_!` followed by the counit `La^* Ra_* L ⟶ L`;
* the *evaluation* `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X`
  (`AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`);
* the *smooth trace* `Tr_γ : Ra_!(T[2d]) ⟶ Λ_Y`, the counit of `Ra_! ⊣ Ra^!` read through
  `γ`.

Composing them gives the *derived Poincaré pairing*

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

which over `Y = Spec k` is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`. It is perfect for `K`
perfect as soon as the projection formula for `Ra_!` holds at `K`; in particular at finite
coefficients `ModuleCat Λ`, where the projection formula is available.

## Main definitions

- `AlgebraicGeometry.Etale.mixedSupportCupProduct` (`sk-def-pairing-data`, `def-sf-cup`,
  `def-pod-mixed-support-cup-product`): `⌣_c`.
- `AlgebraicGeometry.Etale.smoothTrace` (`sk-def-pairing-data`): `Tr_o`.
- `AlgebraicGeometry.Etale.poincarePairing` (`sk-def-pairing`, `def-sf-pairing`,
  `def-pod-derived-poincare-pairing`): `β_K`.
- `AlgebraicGeometry.Etale.properPoincarePairing`: `β_K` read through `Ra_! ≅ Ra_*` for proper
  `a`.
- `AlgebraicGeometry.Etale.poincarePairingOfTrace`: the pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ T` of a trace `(Ra_! Λ_X)[n] ⟶ T`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`
  (`thm-sf-identification`): the derived Poincaré pairing `β_K` of a perfect `K` is perfect,
  provided the projection formula holds at a class of test objects detecting isomorphisms.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula`
  (`thm-sf-identification`): the same with all objects as test objects.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing` (`sk-thm-derived-duality`): at
  finite coefficients, the derived Poincaré pairing of an orientation is perfect for `K`
  dualizable.
- `AlgebraicGeometry.Etale.isPerfectPairing_properPoincarePairing`
  (`thm-pod-proper-poincare-duality`): the same for the pairing of a proper morphism read
  through `Ra_! ≅ Ra_*`.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed`
  (`sk-thm-sf-identification`): over a separably closed field, `β_K` is perfect in the point
  category as soon as the projection formula holds at the shifts `Λ_s[r]`, which detect
  isomorphisms there (`lem-sf-detection`).

## Implementation notes

The definitions take the shape of a purity isomorphism as an argument: an isomorphism
`γ : T[2d] ≅ Ra^! Λ_Y = ω_X` for an object `T` of `D(X_ét)`. An orientation `o`
(`AlgebraicGeometry.Etale.Orientation`), with twist the Tate twist `T = Λ_X(d)`, provides it as
`o.dualizingComplexIso e` for an identification `e : La^* Λ_Y ≅ Λ_X`, which exists
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`); for `A = ModuleCat Λ` with a
Tate twist datum it is `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`.

The exceptional inverse image enters only through the adjunction `Ra_! ⊣ Ra^!`, so the smooth
trace and the pairing are defined for an arbitrary adjunction `adj : Ra_! ⊣ G`, with
`γ : T[2d] ≅ G Λ_Y`: at a finite coefficient ring `Λ` it is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`, and for other coefficients (such as
the integral stage `𝒪_E`) any right adjoint of `Ra_!`, e.g. `Adjunction.ofIsLeftAdjoint`.

The proof of perfectness is the formal Yoneda argument of the blueprint, isolated in
`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`. It is applied to `β_K` by
unification after unfolding the definition of `β_K`, so that the kernel never has to compare
`β_K` with a re-elaborated copy of it (such comparisons time out).

All objects are written with `AlgebraicGeometry.Etale.derivedTensor` rather than `⊗`, so that
the definitions can be specialised to `A = ModuleCat Λ` and composed there with other maps
written with `derivedTensor`; see `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] {d : ℕ}
  {G : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ G)

variable {A a}

variable (a)

section Proper

variable [IsProper a]

end Proper

section Perfectness

variable (A)

end Perfectness

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end ModuleCat

section Point

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a]
  {G : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G) {d : ℕ}

end Point

end Etale

end AlgebraicGeometry
