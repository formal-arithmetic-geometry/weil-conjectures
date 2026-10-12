/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Affine-local intrinsic flatness implies tensor flatness -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Intrinsic affine-local flatness of a quasi-coherent module implies tensor flatness.
Source: Stacks Project, Tags 01U4 (affine-local flatness) and 05NE (flat stalks).
(blueprint: lem-pc-intrinsic-flat-module-tensor-flat).

Proof: On an affine neighbourhood of each point, evaluate IsFlatOver at equal affine
opens. The identity ring map makes the section module flat over its own coordinate
ring. Quasi-coherence identifies the stalk with its localization, hence each stalk
is flat. Tensor products and exactness are computed on stalks, so tensoring with G
preserves short exact sequences. The argument also applies on an empty scheme and
to the zero module. -/
theorem isFlat_of_isFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) : SheafOfModules.IsFlat G := by
  sorry

end AlgebraicGeometry
