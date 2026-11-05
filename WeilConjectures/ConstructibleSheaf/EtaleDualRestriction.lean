/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Étale restriction of coefficient duals

Source: the local internal Hom argument in the docstring of
`WeilConjectures/ConstructibleSheaf/Monoidal.lean`, `IsFiniteLocallyConstantSheaf.ihom_unit`.
(blueprint: lem-weil-pbc-etale-dual-restriction)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
