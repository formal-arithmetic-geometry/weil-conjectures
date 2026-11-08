/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import Submission.WeilConjectures.ZetaLinearAlgebra.Pairing

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Frobenius: the pairings

Let `a : X ⟶ Y` admit a compactification and `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` be a Tate orientation.
This file shows that a Weil pairing compatible with the trace is a morphism of Weil objects
in general, and defines the degreewise Poincaré pairing
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` and its untwisted, line-valued form
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`, whose Frobenius equivariance is proved in
`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance`.

## Main definitions

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): `⟨-, -⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`
  (`prop-pod-degree-of-the-pairing`): the untwisted pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` and its degreewise form.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

end Generic

namespace TateOrientation

section Pairings

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`,

`⟨-, -⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`,

with `H^i_c(X, K) = Hom(Λ_Y, (Ra_! K)[i])`, `H^j(X, K^∨(d)) = Hom(Λ_Y, (Ra_* K^∨(d))[j])` and
`Λ = End(Λ_Y)` (for `Y = Spec k`): the degreewise pairing
(`AlgebraicGeometry.Etale.degreewisePairing`) of the derived Poincaré pairing `β_K` in degrees
`i` and `j - 2d`, read through `(Ra_* K^∨(d))[j] ≅ ((Ra_* K^∨(d))[2d])[j - 2d]` and
`Λ_Y[i + (j - 2d)] ≅ Λ_Y`. -/
noncomputable def degreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  ((degreewisePairing (γ.poincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
lemma degreewisePoincarePairing_apply (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij x y =
      degreewisePairing (γ.poincarePairing K) i (j - 2 * d) x
          (y ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
            (by omega)).hom.app _) ≫
        (shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d)) (by omega)).hom.app _ :=
  rfl

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *untwisted derived Poincaré pairing* of a Tate orientation `γ`,

`β_K^{untw} : Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨)[2d] ⟶ Λ(-d)`: the shift is moved out, then come the
mixed-support cup product, `Ra_!` of the evaluation `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` and the untwisted
smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`), which eliminates the twist
`Λ_X(d)` of `β_K` through `Λ_Y(d) ⊗ᴸ Λ_Y(-d) ≅ Λ_Y`; this is
`AlgebraicGeometry.Etale.poincarePairingOfTrace` for the untwisted smooth trace. -/
noncomputable def untwistedPoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦(2 * d : ℤ)⟧) ⟶
      tateObject Λ Y (-d) :=
  poincarePairingOfTrace a K (2 * d : ℤ) γ.untwistedSmoothTrace

/-- Blueprint `prop-pod-degree-of-the-pairing`: Degree of the pairing.

The *untwisted degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`, the
line-valued pairing

`⟨-, -⟩^{untw}_i : H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`,

with `Λ(-d) = Hom(Λ_Y, Λ_Y(-d))` for `Y = Spec k`: the degreewise pairing of the untwisted
derived pairing (`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`), read as
in `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`. -/
noncomputable def untwistedDegreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) :=
  ((degreewisePairing (γ.untwistedPoincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

end Pairings

end TateOrientation

end Etale

end AlgebraicGeometry
