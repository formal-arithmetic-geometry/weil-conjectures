/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ExistsGluedInvertible
import WeilConjectures.AlgebraicGeometry.ExistsGluedSection

/-!
# Gluing invertible modules and sections across components

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE
(varieties-lemma-glue-invertible-sheaves) (blueprint: lem-sc-glue-component-line-bundles).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
