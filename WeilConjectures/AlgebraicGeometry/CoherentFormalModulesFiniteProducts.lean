/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesBinaryProducts
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesEmptyProducts

/-! # CoherentFormalModulesFiniteProducts

## References

* Stacks Project, Tag 087X
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Coherent adic inverse systems are closed under ambient finite products
(Stacks, Tags 087V and 087X). -/
theorem coherentFormalModules_closedUnderFiniteProducts (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderFiniteProducts := by
  have hempty : (IsCoherentFormalModule I).IsClosedUnderLimitsOfShape
      (Discrete PEmpty) := coherentFormalModules_closedUnderEmptyProducts X I
  have hbin : (IsCoherentFormalModule I).IsClosedUnderBinaryProducts :=
    coherentFormalModules_closedUnderBinaryProducts X I
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

end AlgebraicGeometry
