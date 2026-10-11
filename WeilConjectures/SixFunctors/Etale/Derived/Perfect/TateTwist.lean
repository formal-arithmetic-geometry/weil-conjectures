/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The internal hom and the Tate twists

Let `Λ` be a finite coefficient ring with a Tate twist datum (`HasTateTwist Λ`), with twisting
objects `Λ_X(m) = tateObject Λ X m`. Each `Λ_X(m)` is invertible for `- ⊗ᴸ -`
(`AlgebraicGeometry.Etale.isInvertible_tateObject`), so the internal
hom commutes with the Tate twist: the canonical map
`RHom(K, M) ⊗ᴸ Λ_X(m) ⟶ RHom(K, M ⊗ᴸ Λ_X(m))` is an isomorphism, and
`RHom(K, Λ_X(m)[n]) ≅ K^∨(m)[n]`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_tateObject` (`lem-sf-twist-interchange`)
- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_tateObject_shift` (`lem-sf-twist-interchange`)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] (X : Scheme.{u})

/-- Blueprint `lem-sf-twist-interchange`: Internal Hom with an invertible twist.

For all `K, M ∈ D(X_ét, Λ)` and `m ∈ ℤ` the canonical map
`RHom(K, M) ⊗ᴸ Λ_X(m) ⟶ RHom(K, M ⊗ᴸ Λ_X(m))`, the transpose of `ev ⊗ 1`, is an
isomorphism; its inverse is the map `RHom(K, M ⊗ᴸ Λ_X(m)) ⟶ RHom(K, M) ⊗ᴸ Λ_X(m)` of the
blueprint. That `Λ_X(m)` is invertible is `AlgebraicGeometry.Etale.isInvertible_tateObject`.
The blueprint takes `K` perfect and `M ∈ D^b_{ctf}(X, Λ)`; neither hypothesis is needed. -/
theorem isIso_derivedHomTensorMap_tateObject (K M : DerivedCategoryModule Λ X) (m : ℤ) :
    IsIso (DerivedCategory.derivedHomTensorMap K M (tateObject Λ X m)) :=
  DerivedCategory.isIso_derivedHomTensorMap K
    ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X m)) M

/-- Blueprint `lem-sf-twist-interchange`: Internal Hom with an invertible twist.

For every `K ∈ D(X_ét, Λ)` and `m, n ∈ ℤ`, `RHom(K, Λ_X(m)[n]) ≅ K^∨(m)[n]`, where
`K^∨ = RHom(K, Λ_X)` is the coefficient dual and `(m)` the Tate twist. -/
theorem nonempty_iso_derivedHom_tateObject_shift (K : DerivedCategoryModule Λ X) (m n : ℤ) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((tateObject Λ X m)⟦n⟧) ≅
      ((tateTwist Λ X m).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)))⟦n⟧) :=
  ⟨DerivedCategory.derivedHomIsoCoefficientDualTensor K
      (DerivedCategory.isInvertible_shift
        ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X m)) n) ≪≫
    ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K))).commShiftIso
        n).app (tateObject Λ X m))⟩

end Etale

end AlgebraicGeometry
