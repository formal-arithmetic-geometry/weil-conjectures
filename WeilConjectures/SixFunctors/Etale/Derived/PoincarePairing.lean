/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The derived Poincaré pairing

Let `a : X ⟶ Y` be a morphism admitting a compactification and `o` an orientation of `a` of
relative dimension `d`, with twist `T = Λ_X(d)`. The derived Poincaré pairing is assembled from
three ingredients:

* the *mixed-support cup product* `⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`, the projection map
  of `Ra_!` followed by the counit `La^* Ra_* L ⟶ L`;
* the *evaluation* `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X`
  (`AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`);
* the *smooth trace* `Tr_o : Ra_!(T[2d]) ⟶ Λ_Y`, the counit of `Ra_! ⊣ Ra^!` read through the
  isomorphism `T[2d] ≅ Ra^! Λ_Y` of the orientation.

Composing them gives the *derived Poincaré pairing*

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

which over `Y = Spec k` is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`. Its perfectness
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`) is stated at finite coefficients
`ModuleCat Λ`, where the projection formula for `Ra_!` is available.

## Main definitions

- `AlgebraicGeometry.Etale.mixedSupportCupProduct` (`sk-def-pairing-data`): `⌣_c`.
- `AlgebraicGeometry.Etale.smoothTrace` (`sk-def-pairing-data`): `Tr_o`.
- `AlgebraicGeometry.Etale.poincarePairing` (`sk-def-pairing`): `β_K`.
- `AlgebraicGeometry.Etale.poincarePairingOfTrace`: the pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ T` of a trace `(Ra_! Λ_X)[n] ⟶ T`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing` (`sk-thm-derived-duality`): at
  finite coefficients, the derived Poincaré pairing of an orientation is perfect for `K`
  constructible of finite Tor amplitude and dualizable.

## Implementation notes

The orientation `o` (`AlgebraicGeometry.Etale.Orientation`) gives `La^* Λ_Y ⊗ T[2d] ≅ Ra^! Λ_Y`.
To read it as `T[2d] ≅ Ra^! Λ_Y` the definitions take an identification `e : La^* Λ_Y ≅ Λ_X` as
an argument: it exists (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`), but
the derived pullback is not yet monoidal as a functor, so there is no canonical choice. For
`A = ModuleCat Λ` with a Tate twist datum it is
`AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`.

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

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *mixed-support cup product* of the pairing data,

`⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)` read in `D(Y_ét)`: the projection map of
`Ra_!` followed by `Ra_!` of `K ⊗ᴸ ε_L`, for the counit `ε_L : La^* Ra_* L ⟶ L` of
`La^* ⊣ Ra_*`,
```
                       projection map                              Ra_!(K ⊗ᴸ ε_L)
Ra_! K ⊗ᴸ Ra_* L ───────────────────────▶ Ra_!(K ⊗ᴸ La^* Ra_* L) ─────────────────▶ Ra_!(K ⊗ᴸ L)
```
-/
noncomputable def mixedSupportCupProduct (K L : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj ((R((a)_*[A])).obj L) ⟶
      (R(a)_![A]).obj (((derivedTensor A X).obj K).obj L) :=
  ((projectionMap A a).app K).app ((R((a)_*[A])).obj L) ≫
    (R(a)_![A]).map (((derivedTensor A X).obj K).map
      ((derivedUpperStarLowerStarAdjunction A a).counit.app L))

variable {A a}

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *smooth trace* of the pairing data, `Tr_o : Ra_!(T[2d]) ⟶ Λ_Y` for the twist `T` of the
orientation `o`: the counit of `Ra_! ⊣ Ra^!` at `Λ_Y`, read through the isomorphism
`T[2d] ≅ Ra^! Λ_Y` of `o` (`AlgebraicGeometry.Etale.Orientation.dualizingComplexIso`),
```
               Ra_!(o.dualizingComplexIso e)                   counit
Ra_!(T[2d]) ──────────────────────────────▶ Ra_! Ra^! Λ_Y ──────────▶ Λ_Y
```
It is the normalized trace of the blueprint when `o` is the normalized orientation. -/
noncomputable def smoothTrace (o : Orientation A a d) (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :
    (R(a)_![A]).obj (o.twist⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (R(a)_![A]).map (o.dualizingComplexIso e).hom ≫
    (rightDerivedUpperShriekAdjunction A a).counit.app (𝟙_ _)

/-- The *twisted evaluation* `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` for an object `T` of `D(X_ét)`,
```
                     α⁻¹                         ev_K ⊗ᴸ T                  λ
K ⊗ᴸ (K^∨ ⊗ᴸ T) ─────────▶ (K ⊗ᴸ K^∨) ⊗ᴸ T ───────────────▶ Λ_X ⊗ᴸ T ─────▶ T
```
For `T = Λ_X(d)` it is `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`. -/
noncomputable def twistedEvaluation (T K : 𝐃(X, A)) :
    ((derivedTensor A X).obj K).obj
        (((derivedTensor A X).obj ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ⟶
      T :=
  (derivedTensorAssociator A X _ _ _).inv ≫
    ((derivedTensor A X).map (DerivedCategory.coefficientEvaluation K)).app T ≫
      (derivedTensorLeftUnitor A X T).hom

variable (a)

/-- The unshifted core of the derived Poincaré pairing,
```
                          ⌣_c                                Ra_!(twisted evaluation)
Ra_! K ⊗ᴸ Ra_*(K^∨ ⊗ᴸ T) ─────▶ Ra_!(K ⊗ᴸ (K^∨ ⊗ᴸ T)) ────────────────────────────▶ Ra_! T
```
-/
noncomputable def poincarePairingEvaluation (T K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        ((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T)) ⟶
      (R(a)_![A]).obj T :=
  mixedSupportCupProduct A a _ _ ≫ (R(a)_![A]).map (twistedEvaluation T K)

/-- Blueprint `sk-def-pairing`: The derived pairing, and perfectness of a pairing.

The *derived Poincaré pairing* of an orientation `o` with twist `T`,

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` read in `D(Y_ét)`: the shift is moved out, then
come the mixed-support cup product, `Ra_!` of the twisted evaluation, the shift compatibility
of `Ra_!` and the smooth trace,
```
                              shift out                                    (⌣_c)[2d]
Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ─────────▶ (Ra_! K ⊗ᴸ Ra_*(K^∨ ⊗ᴸ T))[2d] ──────────▶
                                   (Ra_!(ev))[2d]                ≅                      Tr_o
  (Ra_!(K ⊗ᴸ (K^∨ ⊗ᴸ T)))[2d] ─────────────────▶ (Ra_! T)[2d] ─────▶ Ra_!(T[2d]) ──────▶ Λ_Y
```
The blueprint asks `K` to be perfect over `Λ_X`; the composite makes sense for every `K`. -/
noncomputable def poincarePairing (o : Orientation A a d) (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _)
    (K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj o.twist))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (poincarePairingEvaluation a o.twist K)⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![A]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ smoothTrace o e

/-- The *pairing of a trace* `t : (Ra_! Λ_X)[n] ⟶ T`,

`Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ T`:

the shift is moved out, then come the mixed-support cup product, `Ra_!` of the evaluation
`ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` and `t`,
```
                          shift out                             (⌣_c)[n]
Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ─────────▶ (Ra_! K ⊗ᴸ Ra_* K^∨)[n] ─────────▶
                                (Ra_!(ev_K))[n]                t
  (Ra_!(K ⊗ᴸ K^∨))[n] ─────────────────▶ (Ra_! Λ_X)[n] ──────▶ T
```
For the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` of a Tate orientation this is the
untwisted, line-valued Poincaré pairing
(`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`). -/
noncomputable def poincarePairingOfTrace (K : 𝐃(X, A)) {T : 𝐃(Y, A)} (n : ℤ)
    (t : ((R(a)_![A]).obj (𝟙_ _))⟦n⟧ ⟶ T) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj ((DerivedCategory.coefficientDual A X).obj (op K)))⟦n⟧) ⟶ T :=
  ((((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso n).hom.app _ ≫
    (mixedSupportCupProduct A a K _ ≫
      (R(a)_![A]).map (DerivedCategory.coefficientEvaluation K))⟦n⟧') ≫ t

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ Y]

/-- Blueprint `sk-thm-derived-duality`: Derived Poincaré duality.

**The derived pairing is perfect.** For a finite coefficient ring `Λ` whose exponent is
invertible on `Y`, an orientation `o` of `a : X ⟶ Y` with twist `T`, and
`K ∈ D^b_{ctf}(X, Λ)` dualizable (perfect over `Λ_X`), the derived Poincaré pairing `β_K`
(`AlgebraicGeometry.Etale.poincarePairing`) is perfect: its tensor–internal-hom adjoint

`(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`

is an isomorphism. Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`. -/
theorem isPerfectPairing_poincarePairing (o : Orientation (ModuleCat.{u + 1} Λ) a d)
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) :
    IsPerfectPairing (poincarePairing a o e K) :=
  -- Proof sketch: the adjoint is the composite of `K^∨ ⊗ᴸ T[2d] ≅ RHom(K, Ra^! Λ_Y) = 𝔻_X K`,
  -- by the orientation and the dualizability of `K`, with global Verdier duality
  -- `Ra_* RHom(K, Ra^! Λ_Y) ≅ RHom(Ra_! K, Λ_Y)`, the adjunction `Ra_! ⊣ Ra^!` internalised by
  -- the projection formula
  -- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek`.
  -- The projection formula is what needs `Λ` finite, its exponent invertible on `Y` and `K`
  -- constructible.
  sorry

end ModuleCat

end Etale

end AlgebraicGeometry
