/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The Picard group of a scheme

The Picard group of a scheme `X` is the set of isomorphism classes of invertible
`𝒪_X`-modules, with the tensor product as group law.

Since `AlgebraicGeometry.Scheme.Modules.tensorObj` is still a placeholder, no `CommGroup`
instance is provided and `AlgebraicGeometry.Scheme.Pic` is only a type.

## Implementation notes

`X.Modules` lives in `Type (u + 1)`, so `X.Pic` as defined here does too, even though `Pic X`
is really a small group. Until a small model is available (for example a quotient of a type of
transition cocycles, or a `Small` instance allowing `Shrink`), `X.Pic` cannot be the value of a
`GrpCat.{u}`-valued functor, which is what the relative Picard functor of a curve wants to be.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic`: the Picard group of `X`, as a type.
- `AlgebraicGeometry.Scheme.Pic.mk`: the class of an invertible module.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The Picard group of a scheme `X`: the isomorphism classes of invertible `𝒪_X`-modules.

The group structure is the tensor product; since
`AlgebraicGeometry.Scheme.Modules.tensorObj` is still a placeholder, no `CommGroup` instance is
provided here. -/
def Scheme.Pic (X : Scheme.{u}) : Type (u + 1) :=
  Quotient (Setoid.comap
    (Subtype.val : {M : X.Modules // Scheme.Modules.IsInvertible M} → X.Modules)
    (isIsomorphicSetoid X.Modules))

/-- The class in the Picard group of an invertible `𝒪_X`-module. -/
def Scheme.Pic.mk {X : Scheme.{u}} (M : X.Modules) [hM : Scheme.Modules.IsInvertible M] :
    X.Pic :=
  Quotient.mk _ ⟨M, hM⟩

end AlgebraicGeometry
