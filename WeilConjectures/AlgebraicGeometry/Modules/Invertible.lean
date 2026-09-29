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
- The symmetric monoidal category structure on `X.Modules`, from
  `SheafOfModules.monoidalCategory`: the tensor product `M ⊗ N` is the tensor product over
  `𝒪_X`, the sheafification of the tensor product of the underlying presheaves of modules.
- `AlgebraicGeometry.Scheme.Modules.tensorObj`: the tensor product `M ⊗_{𝒪_X} N`, i.e. `M ⊗ N`,
  with scoped notation `M ⊗ₘ N`.
- `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor power `M^{⊗ n}`.
- `AlgebraicGeometry.Scheme.Modules.overPullback`: pullback along a morphism of schemes over a
  base.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- An `𝒪_X`-module is *invertible* if every point has an open neighbourhood on which it
restricts to the structure sheaf. -/
class IsInvertible (M : X.Modules) : Prop where
  /-- Every point has an open neighbourhood on which `M` restricts to the structure sheaf. -/
  exists_isoUnit : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _)

/-- The monoidal category structure on `𝒪_X`-modules: the tensor product over `𝒪_X`.
This uses that `X.ringCatSheaf` is by definition the underlying sheaf of rings
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` of `X.sheaf`. -/
noncomputable instance : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

/-- The monoidal category structure on `𝒪_X`-modules is symmetric. -/
noncomputable instance : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

/-- The tensor product `M ⊗_{𝒪_X} N` of two `𝒪_X`-modules: the sheafification of the tensor
product of the underlying presheaves of modules (`SheafOfModules.tensorObjIsoSheafification`).
It is the tensor product `M ⊗ N` of the monoidal category `X.Modules`. -/
-- TODO(unify): sk-def-picard-pic
noncomputable abbrev tensorObj (M N : X.Modules) : X.Modules :=
  M ⊗ N

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => AlgebraicGeometry.Scheme.Modules.tensorObj

/-- Pullback of an `𝒪_B`-module along a morphism `f : A ⟶ B` of schemes over a base `S`. -/
noncomputable abbrev overPullback {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    (L : B.left.Modules) : A.left.Modules :=
  (Scheme.Modules.pullback f.left).obj L

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module: `M^{⊗ 0} = 𝟙_ X.Modules` and
`M^{⊗ (n + 1)} = M ⊗ M^{⊗ n}`. -/
noncomputable def tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => M ⊗ tensorPow M n

@[simp]
lemma tensorPow_zero (M : X.Modules) : M.tensorPow 0 = 𝟙_ X.Modules :=
  rfl

lemma tensorPow_succ (M : X.Modules) (n : ℕ) : M.tensorPow (n + 1) = M ⊗ M.tensorPow n :=
  rfl

end Scheme.Modules

end AlgebraicGeometry
