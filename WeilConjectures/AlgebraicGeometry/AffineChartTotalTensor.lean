/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Total tensor complexes through the canonical affine chart

Source: Stacks Project, Tag 08DX(2), the underived total-complex comparison.
(blueprint: lem-pc-affine-chart-total-tensor).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
