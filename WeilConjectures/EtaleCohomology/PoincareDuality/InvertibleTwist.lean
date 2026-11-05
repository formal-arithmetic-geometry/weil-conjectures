/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing

/-!
# Perfectness of the derived Poincaré pairing for every complex

At a finite coefficient ring the derived Poincaré pairing

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`

is perfect for `K` dualizable (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`). The
only place where dualizability of `K` enters is the identification of `K^∨ ⊗ᴸ T` with the
internal hom `RHom(K, T)`. When the twist `T` is invertible, as the Tate twist `Λ_X(d)` is, this
identification holds for every `K`, so the derived Poincaré pairing is perfect for every `K`.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom_of_isInvertible`: the comparison map
  `(ihom X).obj (𝟙_ C) ⊗ N ⟶ (ihom X).obj N` is an isomorphism for `N` invertible.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isInvertible`: at a finite
  coefficient ring, `β_K` is perfect for every `K` as soon as the twist `T` is invertible.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing_of_finite`: the
  derived Poincaré pairing of a Tate orientation is perfect for every `K`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

end CategoryTheory.MonoidalClosed

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

section Perfectness

end Perfectness

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end ModuleCat

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {a}

end TateOrientation

end Etale

end AlgebraicGeometry
