/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.Monoidal.Closed.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
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

which over `Y = Spec k` is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`. It is perfect as soon as `K`
is dualizable and the projection formula holds for `Ra_!` at `K`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula`); in
particular at finite coefficients `ModuleCat Λ`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`).

## Main definitions

- `AlgebraicGeometry.Etale.mixedSupportCupProduct` (`sk-def-pairing-data`): `⌣_c`.
- `AlgebraicGeometry.Etale.smoothTrace` (`sk-def-pairing-data`): `Tr_o`.
- `AlgebraicGeometry.Etale.poincarePairing` (`sk-def-pairing`): `β_K`.
- `AlgebraicGeometry.Etale.properPoincarePairing`: `β_K` read through `Ra_! ≅ Ra_*` for proper
  `a`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula`: the
  derived Poincaré pairing of a dualizable `K` is perfect if the projection formula holds.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`
  (`thm-pod-derived-poincare-duality`): at finite coefficients, the derived Poincaré pairing of
  an orientation is perfect for `K` constructible of finite Tor amplitude and dualizable.
- `AlgebraicGeometry.Etale.isPerfectPairing_properPoincarePairing`
  (`thm-pod-proper-poincare-duality`): the same for the pairing of a proper morphism read
  through `Ra_! ≅ Ra_*`.

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

The mixed-support cup product, the twisted evaluation and the derived Poincaré pairing are the
instances at `La^* ⊣ Ra_*` and `Ra_! ⊣ Ra^!` of the constructions
`CategoryTheory.Adjunction.mixedCupProduct`, `CategoryTheory.MonoidalClosed.twistedEvaluation`
and `CategoryTheory.Adjunction.poincarePairing` for abstract adjunctions, and perfectness is
`CategoryTheory.Adjunction.isPerfectPairing_poincarePairing`. Proving it directly in `D(X_ét)`
is impractical: unfolding the definitions there produces composites whose implicit objects
differ by auxiliary proof terms, which the kernel only compares after unfolding the composition
of the derived category.
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
  (derivedUpperStarLowerStarAdjunction A a).mixedCupProduct (R(a)_![A])
    ((projectionMap A a).app K) L

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
  MonoidalClosed.twistedEvaluation K T

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
  (derivedUpperStarLowerStarAdjunction A a).poincarePairing (R(a)_![A])
    ((projectionMap A a).app K) (rightDerivedUpperShriekAdjunction A a) (2 * d : ℤ) o.twist
    (o.dualizingComplexIso e)

omit [HasSmallSiteSheafify A] in
variable {a} in
/-- Derived Poincaré duality for a general coefficient category: if `K` is dualizable and the
projection formula holds for `a` at `K` and every object of `D(Y_ét)`, then the derived
Poincaré pairing `β_K` is perfect. This is
`CategoryTheory.Adjunction.isPerfectPairing_poincarePairing`, the formal Yoneda argument. -/
theorem isPerfectPairing_poincarePairing_of_hasProjectionFormula (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) {K : 𝐃(X, A)} (hK : IsDualizable K)
    (hPF : ∀ L, HasProjectionFormula A a K L) :
    IsPerfectPairing (poincarePairing a o e K) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  exact Adjunction.isPerfectPairing_poincarePairing _ _ _ _ _ _ _ Kᘁ hPF

section Proper

variable [IsProper a]

/-- The derived Poincaré pairing of a proper morphism `a`, read through the identification
`Ra_! ≅ Ra_*` of `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`:

`Ra_* K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

that is `RΓ(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` over `Y = Spec k`. -/
noncomputable def properPoincarePairing (o : Orientation A a d)
    (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) (K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R((a)_*[A])).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj o.twist))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar A a).inv.app K ▷ _ ≫ poincarePairing a o e K

omit [HasSmallSiteSheafify A] in
variable {a} in
/-- If the derived Poincaré pairing of a proper morphism is perfect, so is the pairing
`AlgebraicGeometry.Etale.properPoincarePairing` read through `Ra_! ≅ Ra_*`. -/
theorem IsPerfectPairing.properPoincarePairing {o : Orientation A a d}
    {e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _} {K : 𝐃(X, A)}
    (h : IsPerfectPairing (poincarePairing a o e K)) :
    IsPerfectPairing (properPoincarePairing a o e K) :=
  MonoidalClosed.IsPerfectPairing.whiskerRight_comp h _

end Proper

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `thm-pod-derived-poincare-duality`: Derived Poincaré duality.

**The derived pairing is perfect.** For a finite coefficient ring `Λ` whose exponent is
invertible on `Y`, an orientation `o` of `a : X ⟶ Y` with twist `T`, and
`K ∈ D^b_{ctf}(X, Λ)` dualizable (perfect over `Λ_X`), the derived Poincaré pairing `β_K`
(`AlgebraicGeometry.Etale.poincarePairing`) is perfect: its tensor–internal-hom adjoint

`(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`

is an isomorphism. Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`. -/
theorem isPerfectPairing_poincarePairing [HasInvertibleExponent Λ Y]
    (o : Orientation (ModuleCat.{u + 1} Λ) a d)
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) {K : DerivedCategoryModule Λ X}
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) :
    IsPerfectPairing (poincarePairing a o e K) :=
  isPerfectPairing_poincarePairing_of_hasProjectionFormula o e hKd fun L ↦
    hasProjectionFormula_of_finite Λ a K L

/-- Blueprint `thm-pod-proper-poincare-duality`: Proper Poincaré duality.

For `a` proper, a finite coefficient ring `Λ` whose exponent is invertible on `Y` and
`K ∈ D^b_{ctf}(X, Λ)` dualizable, the derived Poincaré pairing read through `Ra_! ≅ Ra_*`,

`Ra_* K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`

(`AlgebraicGeometry.Etale.properPoincarePairing`), is perfect. Over `Y = Spec k` this is
`RΓ(X, K^∨(d))[2d] ≅ RΓ(X, K)^∨`. -/
theorem isPerfectPairing_properPoincarePairing [IsProper a] [HasInvertibleExponent Λ Y]
    (o : Orientation (ModuleCat.{u + 1} Λ) a d)
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) :
    IsPerfectPairing (properPoincarePairing a o e K) :=
  (isPerfectPairing_poincarePairing a Λ o e hK hKd).properPoincarePairing

end ModuleCat

end Etale

end AlgebraicGeometry
