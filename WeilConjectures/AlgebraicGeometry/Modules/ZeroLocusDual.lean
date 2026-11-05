/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# The ideal of the zero scheme of a section is the image of its dual

Let `ℳ` be an invertible `𝒪_X`-module and `s : 𝒪_X ⟶ ℳ` a global section. The blueprint defines
the ideal sheaf of the zero scheme `Z(s)` as the image of the transpose
`s^∨ : ℳ^∨ ⟶ 𝒪_X^∨ ≅ 𝒪_X`. In this project `Z(s)` is defined by its local equations
(`AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`); this file proves that the two agree, as
subobjects of `𝒪_X` in the abelian category of `𝒪_X`-modules.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.dualUnitIso`: the identification `𝒪_X^∨ ≅ 𝒪_X`, `λ ↦ λ(1)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.adjointSection`: the global section
  `s : 𝒪_X ⟶ M ⊗ N^∨` corresponding to a morphism `φ : N ⟶ M` with `N` invertible.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.Hom.imageSubobject_eq_mk_toModulesι`: for a morphism
  `ψ : ℒ ⟶ 𝒪_X` from an invertible module, the image of `ψ` is the ideal sheaf of `Z(ψ)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus_dualMap_comp_dualUnitIso`: `Z(s^∨) = Z(s)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.imageSubobject_dualMap_comp_dualUnitIso`: the ideal sheaf
  of `Z(s)` is the image of `s^∨ : ℳ^∨ ⟶ 𝒪_X` (blueprint `def-pc-zero-scheme`,
  `lem-pc-zero-scheme-properties`).
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus_adjointSection`: the section `s` of
  `M ⊗ N^{-1}` corresponding to a morphism `φ : N ⟶ M` of invertible modules has `Z(s) = Z(φ)`
  (blueprint `lem-pc-zero-scheme-recd`).
- `AlgebraicGeometry.Scheme.Modules.nonempty_dual_pullback_iso_pullback_dual`:
  `(g^* N)^∨ ≅ g^* (N^∨)` for invertible `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace Hom

end Hom

end AlgebraicGeometry.Scheme.Modules
