/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules on a scheme and their tensor product

An `𝒪_X`-module is *invertible* if it is locally isomorphic to `𝒪_X`.

Mathlib does not yet have a tensor product of sheaves of modules (only the presheaf-level one,
`PresheafOfModules.Monoidal`), so `AlgebraicGeometry.Scheme.Modules.tensorObj` is declared here
as an `opaque` constant, to be replaced by the real construction once the monoidal structure on
`SheafOfModules` lands. Being `opaque` rather than `sorry`-bodied, it genuinely depends on its
two arguments and introduces no `sorryAx`; but it satisfies no equations whatsoever, so **no
statement mentioning `tensorObj` can be proved before it is replaced**. The same warning applies
to `tensorPow`, which is defined by iterating it.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsInvertible`: an `𝒪_X`-module locally isomorphic to `𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N` (placeholder),
  with scoped notation `M ⊗ₘ N`.
- `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor power `M^{⊗ n}`.
- `AlgebraicGeometry.Scheme.Modules.overPullback`: pullback along a morphism of schemes over a
  base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *invertible* if every point has an open neighbourhood on which it
restricts to the structure sheaf. -/
class IsInvertible (M : X.Modules) : Prop where
  /-- Every point has an open neighbourhood on which `M` restricts to the structure sheaf. -/
  exists_isoUnit : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _)

/-- The tensor product `M ⊗_{𝒪_X} N` of two `𝒪_X`-modules: the sheafification of the tensor
product of the underlying presheaves of modules.

The monoidal structure on sheaves of modules is not available in Mathlib yet, so this is an
`opaque` placeholder: it satisfies no equations, and no statement mentioning it can be proved
before it is replaced by the real construction. -/
-- TODO(unify): sk-def-picard-pic
opaque tensorObj (M N : X.Modules) : X.Modules := M

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module. Since it is defined by iterating the
placeholder `AlgebraicGeometry.Scheme.Modules.tensorObj`, it too satisfies no equations for
`n ≥ 1`. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit _
  | n + 1 => tensorObj M (tensorPow M n)

end Scheme.Modules

end AlgebraicGeometry
