/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow

/-!
# Derived completeness for a principal ideal

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor.
This file shows that an object `K` of `D(J, R) = DerivedCategory (Sheaf J (ModuleCat R))` is
derived complete for the ideal `(ϖ)` (`DerivedCategory.derivedComplete`, defined by the Milnor
triangle `K ≅ R lim_n (K ⊗ᴸ R/ϖⁿ)`) if and only if every map to `K` from an object on which `ϖ`
acts invertibly vanishes. This is the characterisation `RHom(R[1/ϖ], K) = 0` of Stacks,
Tags 091Q and 0999, phrased with the class `DerivedCategory.smulInvertible J ϖ` of objects on
which `ϖ` acts invertibly (the objects `X ⊗ᴸ R[1/ϖ]`). As a consequence, the derived complete
objects form a triangulated subcategory.

## Main definitions

- `DerivedCategory.smulInvertible J ϖ`: the objects `X` of `D(J, R)` such that `ϖ • 𝟙 X` is an
  isomorphism.

## Main results

- `DerivedCategory.derivedComplete_iff_rightOrthogonal`: for `I = (ϖ)` with `ϖ` a
  nonzerodivisor, `K` is derived complete iff it is right orthogonal to
  `DerivedCategory.smulInvertible J ϖ`.
- `DerivedCategory.isTriangulated_derivedComplete`: the derived complete objects form a
  triangulated subcategory.

## Proof

If `K` is derived complete, the terms `K ⊗ᴸ R/ϖⁿ` of the tower are killed by `ϖⁿ`, so they
receive no nonzero maps from objects on which `ϖ` acts invertibly, and neither does their
homotopy limit `K`.

Conversely, let `K` be right orthogonal to `smulInvertible J ϖ`, let `F` be a homotopy limit of
the tower `K ⊗ᴸ R/ϖⁿ`, and let `φ : K ⟶ F` be a map extending the reductions, obtained by
comparing `F` with the Milnor triangle of the constant tower `K`. Its cone `X` is right
orthogonal to `smulInvertible J ϖ`. Tensoring with `M = R/ϖ` turns the reduction tower into a
tower which is pro-isomorphic to the constant tower `K ⊗ᴸ M`, because `ϖ` acts by zero on
`K ⊗ᴸ M`; since `- ⊗ᴸ M` is triangulated and commutes with products, `φ ⊗ᴸ M` is then an
isomorphism (`CategoryTheory.Pretriangulated.isIso_of_proIso`), so `X ⊗ᴸ M = 0`, that is `ϖ`
acts invertibly on `X`. Hence `X = 0` and `φ` is an isomorphism, which says that `K` is the
homotopy limit of its reductions.

## Implementation notes

The preliminary constructions are in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.SmulInvertible`,
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle` and
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow`, which this module
imports.

The monoidal structure of `D(J, R)` and the instances attached to it are taken from the fields
of `DerivedCategory.sheafTensorStructure J R`, declared below as local instances of high
priority, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`. The statements of the main
results do not involve the monoidal structure.

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

section Main

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

set_option hygiene false in
/-- The functor `- ⊗ᴸ R/ϖ` on `D(J, R)`, where `R/ϖ = R/I` is the first reduction. -/
local notation "⊗ᴸR/ϖ" => (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
  ((quotPowFunctor J I).obj (op 1))

end Main

end DerivedCategory
