/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# The zero locus of a morphism of invertible modules is locally principal

Source: `WeilConjectures/AlgebraicGeometry/Modules/ZeroLocus.lean`, theorem
`Hom.isLocallyPrincipal_zeroLocus`, lines 570–576
(blueprint: lem-pc-zero-scheme-locally-principal).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The zero locus of a morphism between invertible `𝒪_X`-modules is locally principal.
Source: `WeilConjectures/AlgebraicGeometry/Modules/ZeroLocus.lean`, theorem
`Hom.isLocallyPrincipal_zeroLocus`, lines 570–576.
(blueprint: lem-pc-zero-scheme-locally-principal)

Proof: First convert `M.IsInvertible` and `N.IsInvertible` to
`SheafOfModules.IsInvertible` using `IsInvertible.sheafOfModules_isInvertible`
(lem-pc-invertible-sheaf-instance). For each point `x`, apply `exists_isFreeGenerator₂`
with `W = ⊤` to find an affine neighbourhood `U` with free generators `eM` and `eN`
(lem-pc-invertible-common-free-generator). The generator `eN` gives a coefficient
`b` with `φ(eM) = b • eN`. Then `Hom.ideal_zeroLocus` identifies the ideal on `U`
with `Ideal.span {b}` (lem-pc-zero-scheme-ideal-local). Thus `U` and `b` witness
local principality at `x`; since `x` was arbitrary, the zero locus is locally principal. -/
theorem Hom.isLocallyPrincipal_zeroLocus_of_isInvertible {X : Scheme.{u}}
    {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (φ : M ⟶ N) :
    φ.zeroLocus.IsLocallyPrincipal := by
  sorry

end AlgebraicGeometry.Scheme.Modules
