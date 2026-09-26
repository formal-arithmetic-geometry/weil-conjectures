/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Skeletal

/-!
# Invertible modules on a scheme and the Picard group

An `𝒪_X`-module is *invertible* if it is locally isomorphic to `𝒪_X`, and the Picard group of
`X` is the set of isomorphism classes of invertible `𝒪_X`-modules.

Mathlib does not yet have a tensor product of sheaves of modules (only the presheaf-level one,
`PresheafOfModules.Monoidal`), so `AlgebraicGeometry.Scheme.Modules.tensorObj` is recorded here
with a `sorry` body, to be replaced once the monoidal structure on `SheafOfModules` lands. The
same goes for the group structure on the Picard group, which is why the Picard group appears
below as a type rather than as a `CommGroup`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsInvertible`: an `𝒪_X`-module locally isomorphic to `𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N`.
- `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor power `M^{⊗ n}`.
- `AlgebraicGeometry.Scheme.Modules.overPullback`: pullback along a morphism of schemes over a
  base.
- `AlgebraicGeometry.Scheme.Pic`: the Picard group of `X`, as a type.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *invertible* if every point has an open neighbourhood on which it
restricts to the structure sheaf. -/
def IsInvertible (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _)

/-- The tensor product `M ⊗_{𝒪_X} N` of two `𝒪_X`-modules: the sheafification of the tensor
product of the underlying presheaves of modules.

The monoidal structure on sheaves of modules is not available in Mathlib yet, so this is a
placeholder. -/
-- TODO(unify): sk-def-picard-pic
noncomputable def tensorObj (M N : X.Modules) : X.Modules := sorry

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit _
  | n + 1 => tensorObj M (tensorPow M n)

end Scheme.Modules

/-- The Picard group of a scheme `X`: the isomorphism classes of invertible `𝒪_X`-modules.

The group structure is the tensor product; since
`AlgebraicGeometry.Scheme.Modules.tensorObj` is still a placeholder, no `CommGroup` instance is
provided here. -/
def Scheme.Pic (X : Scheme.{u}) : Type (u + 1) :=
  Quotient (Setoid.comap
    (Subtype.val : {M : X.Modules // Scheme.Modules.IsInvertible M} → X.Modules)
    (isIsomorphicSetoid X.Modules))

/-- The class in the Picard group of an invertible `𝒪_X`-module. -/
def Scheme.Pic.mk {X : Scheme.{u}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    X.Pic :=
  Quotient.mk _ ⟨M, hM⟩

end AlgebraicGeometry
