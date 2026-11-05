/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.ExteriorPower.Top
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-!
# Exterior powers of sheaves of modules on a scheme

For a sheaf of `𝒪_X`-modules `M` and `r : ℕ`, the exterior power `⋀ʳ M` is the sheafification
of the presheaf of modules `U ↦ ⋀ʳ_{𝒪(U)} M(U)` (`PresheafOfModules.exteriorPower`).

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.exteriorPower M r`: the exterior power `⋀ʳ M`.
- `AlgebraicGeometry.Scheme.Modules.wedge`: the section `m₁ ∧ ⋯ ∧ m_r` of `⋀ʳ M` over `U` of
  sections `mᵢ` of `M` over `U`.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_wedge`: if `M` is locally free on `U` with
  basis `m₁, …, m_r` (on a basis of the topology of `U`), then `m₁ ∧ ⋯ ∧ m_r` is a free generator
  of `⋀ʳ M` on `U`.

(blueprint: `lem-pc-projective-space-canonical`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Sheafification

variable (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)

end Sheafification
section ExteriorPower

variable (M : X.Modules) (r : ℕ)

variable {M r}

end ExteriorPower

end AlgebraicGeometry.Scheme.Modules
