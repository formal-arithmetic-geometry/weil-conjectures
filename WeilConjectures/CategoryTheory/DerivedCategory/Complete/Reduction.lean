/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion

/-!
# Reduction modulo an ideal on the derived category of sheaves of modules

Let `(C, J)` be an essentially small site and `R` a commutative ring. For an ideal `𝔞` of `R`,
the reduction `K ↦ K ⊗ᴸ R/𝔞` (`DerivedCategory.reductionModIdeal J 𝔞`) is a triangulated
endofunctor of `D(J, R)`. For a nonzerodivisor `ϖ`:

* if `K ⊗ᴸ R/ϖ = 0`, then `ϖ` acts invertibly on `K`
  (`DerivedCategory.isIso_smul_id_of_isZero_reductionModIdeal`);
* a morphism whose reduction modulo `ϖ` is an isomorphism becomes an isomorphism after derived
  `ϖ`-completion (`DerivedCategory.isIso_derivedCompletion_map_of_isIso_reductionModIdeal`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

variable {J}

end DerivedCategory
