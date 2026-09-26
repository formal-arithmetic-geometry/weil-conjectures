/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Perfect
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# The derived Poincaré pairing

The Poincaré pairing is assembled from three ingredients: the *mixed-support cup product*

`⌣_c : RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)`,

the *evaluation* `K ⊗ᴸ K^∨ ⟶ Λ_X`, and the *normalized smooth trace*

`Tr : RΓ_c(X, Λ_X(d)[2d]) ⟶ Λ`,

the counit of `Ra_{X!} ⊣ Ra_X^!` read through an orientation
`γ : Λ_X(d)[2d] ≅ ω_{X,Λ}`. Composing them gives the *derived Poincaré pairing*

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`.

## Main definitions

- `AlgebraicGeometry.ProEtale.mixedSupportCupProduct`: the mixed-support cup product.
- `AlgebraicGeometry.ProEtale.smoothTrace`: the normalized smooth trace.
- `AlgebraicGeometry.ProEtale.poincarePairing`: the derived Poincaré pairing `β_K`.
- `CategoryTheory.MonoidalClosed.IsPerfectPairing`
  (`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`): perfectness of a pairing,
  i.e. that its tensor–internal-hom adjoint is an isomorphism.

## Implementation notes

The *orientation* `γ : Λ_X(d)[2d] ≅ ω_{X,Λ}` is the interface record of the smooth purity
chapter (blueprint `sk-def-sf-orientation`, proved there as `sk-thm-smooth-purity` and
`sk-thm-purity-transport`). It is taken here as a hypothesis rather than constructed.

The value object of the pairing is `RΓ(S, Λ_S)`, which for `Y = Spec k` with `k` separably
closed is `Λ`; writing it this way avoids assuming the comparison `RΓ(s, Λ) ≅ Λ`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *mixed-support cup product*

`⌣_c : RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)`,

the composite of the projection transformation for `Ra_{X!}` with the counit
`La_X^* Ra_{X*} ⟶ id`. -/
noncomputable def mixedSupportCupProduct
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (compactlySupportedGlobalSections A a).obj K ⊗ (rightDerivedGlobalSections A X).obj L ⟶
      (compactlySupportedGlobalSections A a).obj (((-⊗ᴸ-(X)[A]).obj K).obj L) :=
  sorry

/-- Blueprint `sk-def-pairing-data`: The pairing data.

The *normalized smooth trace* `Tr : RΓ_c(X, Λ_X(d)[2d]) ⟶ Λ`: the counit of
`Ra_{X!} ⊣ Ra_X^!` read through the orientation `γ : Λ_X(d)[2d] ≅ ω_{X,Λ}`. -/
noncomputable def smoothTrace (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a) :
    (compactlySupportedGlobalSections A a).obj
        (((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧) ⟶
      (rightDerivedGlobalSections A Y).obj (𝟙_ _) :=
  (rightDerivedGlobalSections A Y).map
    ((R(a)_![A]).map γ.hom ≫ (rightDerivedUpperShriekAdjunction A a).counit.app (𝟙_ _))

/-- Blueprint `sk-def-pairing`: The derived pairing, and perfectness of a pairing.

The *derived Poincaré pairing*

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`,

the mixed-support cup product followed by the twisted evaluation `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)` and
the normalized smooth trace of the orientation `γ`. -/
noncomputable def poincarePairing (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (compactlySupportedGlobalSections A a).obj K ⊗
        ((rightDerivedGlobalSections A X).obj
          ((tateTwist A X (d : ℤ)).obj ((derivedDual A X).obj (op K))))⟦(2 * d : ℤ)⟧ ⟶
      (rightDerivedGlobalSections A Y).obj (𝟙_ _) :=
  sorry

end ProEtale

end AlgebraicGeometry
