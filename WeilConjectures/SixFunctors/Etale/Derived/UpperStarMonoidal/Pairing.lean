/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Pairings of classes and the derived pullback

For `h : Y ⟶ Y`, objects `A₁, B, C` of `D(Y_ét)` with maps `ψ : Lh^*(-) ⟶ (-)` and a pairing
`Q : A₁ ⊗ᴸ B ⟶ C` compatible with them, the product
`Hom(Λ_Y, A₁[i]) × Hom(Λ_Y, B[j]) ⟶ Hom(Λ_Y, C[i + j])` induced by `Q` intertwines the
operators `x ↦ ψ[n] ∘ Lh^* x ∘ ε⁻¹`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_pairing_comm`). This is the Frobenius
equivariance of the degreewise pairing of a Weil pairing.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Y : Scheme.{u}} (h : Y ⟶ Y) [(h)^*[A].PreservesFlat]

end Etale

end AlgebraicGeometry
