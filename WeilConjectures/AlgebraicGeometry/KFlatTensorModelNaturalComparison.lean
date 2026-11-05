/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Natural tensor comparison with a fixed K-flat model
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-kflat-tensor-model-natural-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

end AlgebraicGeometry.Scheme
