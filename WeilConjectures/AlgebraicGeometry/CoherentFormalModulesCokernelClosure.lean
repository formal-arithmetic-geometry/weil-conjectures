/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoInvariant

/-! # CoherentFormalModulesCokernelClosure

Stacks Project, Tag 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Ambient cokernels of maps between coherent adic systems remain coherent adic.
(Stacks, Tag 087X). -/
theorem coherentFormalModules_closedUnderCokernels (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderCokernels := by
  refine ⟨?_⟩
  intro _ ⟨f, k, hk, ⟨hF, hG⟩⟩
  have hc := coherentFormalModules_canonicalCokernel_isCoherent X I hF hG f
  exact coherentFormalModules_of_iso X I (
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) hc

end AlgebraicGeometry
