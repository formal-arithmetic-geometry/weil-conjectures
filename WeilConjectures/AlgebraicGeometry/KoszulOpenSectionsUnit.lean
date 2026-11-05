/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyComparison

/-! # The canonical unit in derived open sections

Source: Stacks Project, Tag 09M1, evaluation at one.
(blueprint: lem-sc-derived-open-structure-sections-unit).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
noncomputable section

end
end AlgebraicGeometry
