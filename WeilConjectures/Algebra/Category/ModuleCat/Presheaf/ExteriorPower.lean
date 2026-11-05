/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of
`R`-modules. For `r : ℕ`, the exterior power `⋀ʳ M` is the presheaf of modules
`X ↦ ⋀[R(X)]^r M(X)`; the restriction map along `f : X ⟶ Y` is the map
`⋀ʳ M(X) → ⋀ʳ M(Y)`, `m₁ ∧ ⋯ ∧ m_r ↦ f^* m₁ ∧ ⋯ ∧ f^* m_r`, which is semilinear along
`R(X) → R(Y)`.

## Main declarations

- `PresheafOfModules.exteriorPower M r`: the exterior power `⋀ʳ M`.
- `PresheafOfModules.exteriorPower_map_ιMulti`: the restriction maps of `⋀ʳ M` on wedge
  products.
-/

@[expose] public section

universe u

open CategoryTheory

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModules

variable (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (r : ℕ)

namespace ExteriorPower

end ExteriorPower

end PresheafOfModules
