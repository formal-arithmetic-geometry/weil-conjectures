/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Invertible modules on a scheme and their tensor product

An `𝒪_X`-module is *invertible* if it is locally isomorphic to `𝒪_X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsInvertible`: an `𝒪_X`-module locally isomorphic to `𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N`,
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
product of the underlying presheaves of modules. -/
-- TODO(unify): sk-def-picard-pic
noncomputable def tensorObj (M N : X.Modules) : X.Modules :=
  SheafOfModules.tensorObj (R := X.sheaf) M N

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit _
  | n + 1 => tensorObj M (tensorPow M n)

end Scheme.Modules

end AlgebraicGeometry
