/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The derived Poincaré pairing

Let `a : X ⟶ s` be a morphism admitting a compactification (for the Poincaré duality
chapter, the structure morphism of the geometric fibre `X` of a `PoincareDualitySetting` over
`s = Spec k`), and let `Λ` be a coefficient ring with a Tate twist. The derived Poincaré
pairing is assembled from three ingredients:

* the *mixed-support cup product* `⌣_c : RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)`, the
  projection map of `Ra_!` followed by the counit `La^* Ra_* L ⟶ L`;
* the *evaluation* `K ⊗ᴸ K^∨ ⟶ Λ_X`, the counit of `K ⊗ᴸ - ⊣ RHom(K, -)` at `Λ_X`;
* the *normalized smooth trace* `Tr : RΓ_c(X, Λ_X(d)[2d]) ⟶ Λ`, the counit of
  `Ra_! ⊣ Ra^!` read through an orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_s`.

Composing them gives the *derived Poincaré pairing*

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`.

As in `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality`, `RΓ_c(X, -)` and `RΓ(X, -)`
are read one step earlier, as `Ra_!` and `Ra_*` with values in `D(s_ét, Λ)`, and `Λ` is the
constant complex `Λ_s`, the unit of `D(s_ét, Λ)`. A pairing is perfect if its tensor–internal-hom
adjoint is an isomorphism (`AlgebraicGeometry.Etale.DerivedCategory.IsPerfectPairing`, which
is `CategoryTheory.MonoidalClosed.IsPerfectPairing` for pairings written with `derivedTensor`).

## Main definitions

- `AlgebraicGeometry.Etale.mixedSupportCupProduct` (`sk-def-pairing-data`): `⌣_c`.
- `AlgebraicGeometry.Etale.smoothTrace` (`sk-def-pairing-data`): `Tr`.
- `AlgebraicGeometry.Etale.poincarePairing` (`sk-def-pairing`): `β_K`.

## Implementation notes

The orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_s` is an explicit argument. It exists by smooth
purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), which only
asserts its existence; the blueprint's normalized orientation is the one built in the purity
chapter.

The coefficients are `ModuleCat Λ` for a commutative ring `Λ` with a Tate twist datum
(`AlgebraicGeometry.Etale.HasTateTwist`). This is the finite stage `A_{E,n}` of the
blueprint; the stages `𝒪_E`, `E` and `ℚ̄_ℓ` are the subject of `sk-thm-transport`.

All objects are written with `AlgebraicGeometry.Etale.derivedTensor` rather than `⊗`, and the
associator is `AlgebraicGeometry.Etale.derivedTensorAssociator`: see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` for why. The composite `β_K` is
split into small definitions, each checked by the kernel on its own.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *mixed-support cup product*

`⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)` read in `D(Y_ét)`: the projection map
`Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ La^* Ra_* L)` of `AlgebraicGeometry.Etale.projectionMap`,
followed by `Ra_!` of `K ⊗ᴸ ε_L` for the counit `ε_L : La^* Ra_* L ⟶ L` of `La^* ⊣ Ra_*`. -/
noncomputable def mixedSupportCupProduct (a : X ⟶ Y) [HasCompactification a]
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj L) ⟶
      (R(a)_![ModuleCat.{u + 1} Λ]).obj (((derivedTensor _ X).obj K).obj L) :=
  ((projectionMap (ModuleCat.{u + 1} Λ) a).app K).app ((R((a)_*[ModuleCat.{u + 1} Λ])).obj L) ≫
    (R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj K).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).counit.app L))

variable [HasTateTwist Λ]

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *normalized smooth trace* `Tr : Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y`, that is
`RΓ_c(X, Λ_X(d)[2d]) ⟶ Λ`: the counit `Ra_! Ra^! Λ_Y ⟶ Λ_Y` of `Ra_! ⊣ Ra^!` read through
the orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y = ω_X`. -/
noncomputable def smoothTrace (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X d).obj (constantComplex Λ X)) ⟶
      𝟙_ _ :=
  (R(a)_![ModuleCat.{u + 1} Λ]).map γ.hom ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) a).counit.app (𝟙_ _)

variable {Λ} in
/-- The *evaluation* `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X`, the counit at `Λ_X` of the adjunction
`K ⊗ᴸ - ⊣ RHom(K, -)`. -/
noncomputable def coefficientEvaluation
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ X).obj K).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) ⟶ 𝟙_ _ :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).counit.app (𝟙_ _)

/-- The *twisted evaluation* `ev_K(d) : K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`: the associator
`K ⊗ᴸ (K^∨ ⊗ᴸ Λ_X(d)) ≅ (K ⊗ᴸ K^∨) ⊗ᴸ Λ_X(d)` followed by `ev_K ⊗ᴸ Λ_X(d)`. Its target is
`Λ_X ⊗ᴸ Λ_X(d)`, the twist `(d)` of `Λ_X`, from which the smooth trace starts. -/
noncomputable def twistedEvaluation (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ X).obj K).obj ((tateTwist Λ X d).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))) ⟶
      (tateTwist Λ X d).obj (constantComplex Λ X) :=
  (derivedTensorAssociator _ X _ _ _).inv ≫
    ((derivedTensor _ X).map (coefficientEvaluation K)).app (tateObject Λ X d)

/-- The unshifted core of the derived Poincaré pairing,

`Ra_! K ⊗ᴸ Ra_*(K^∨(d)) ⟶ Ra_!(K ⊗ᴸ K^∨(d)) ⟶ Ra_!(Λ_X(d))`,

the mixed-support cup product followed by `Ra_!` of the twisted evaluation. -/
noncomputable def poincarePairingEvaluation (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)))) ⟶
      (R(a)_![ModuleCat.{u + 1} Λ]).obj ((tateTwist Λ X d).obj (constantComplex Λ X)) :=
  mixedSupportCupProduct Λ a _ _ ≫ (R(a)_![ModuleCat.{u + 1} Λ]).map (twistedEvaluation Λ d K)

/-- The identification `Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ≅ (Ra_! K ⊗ᴸ Ra_*(K^∨(d)))[2d]`, moving
the shift out of the second factor. -/
noncomputable def poincarePairingShiftIso (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))))⟦(2 * d : ℤ)⟧) ≅
      (((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj
            (op K)))))⟦(2 * d : ℤ)⟧ :=
  (((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).commShiftIso
    (2 * d : ℤ)).app _

/-- The normalized smooth trace precomposed with the shift compatibility of `Ra_!`:
`(Ra_!(Λ_X(d)))[2d] ≅ Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y`. -/
noncomputable def shiftedSmoothTrace (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a) :
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj
        ((tateTwist Λ X d).obj (constantComplex Λ X)))⟦(2 * d : ℤ)⟧ ⟶ 𝟙_ _ :=
  ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ smoothTrace Λ a d γ

/-- Blueprint `sk-def-pairing`: The derived pairing, and perfectness of a pairing.

The *derived Poincaré pairing*

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_Y`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` read in `D(Y_ét)`: the shift is moved out,
then come the mixed-support cup product `⌣_c`, `Ra_!` of the twisted evaluation
`K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`, and the normalized smooth trace of the orientation `γ`,

`β_K = Tr ∘ Ra_!(ev_K(d))[2d] ∘ ⌣_c[2d]`.

The blueprint asks `K` to be perfect over `Λ_X`; the composite makes sense for every `K`. -/
noncomputable def poincarePairing (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : (twistShift Λ X d).obj (constantComplex Λ X) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((tateTwist Λ X d).obj
          ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj
            (op K))))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (poincarePairingShiftIso Λ a d K).hom ≫
    (poincarePairingEvaluation Λ a d K)⟦(2 * d : ℤ)⟧' ≫ shiftedSmoothTrace Λ a d γ

end Etale

end AlgebraicGeometry
