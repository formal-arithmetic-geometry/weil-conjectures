/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Section.SectionAffineOpenKillsCohomology
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerObstruction

/-! # Lifting a tensor power of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, equation (30.17.5.1)
and the boundary calculation following it.
(blueprint: lem-sc-square-zero-section-power-lift).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

end AlgebraicGeometry.Scheme.Modules
