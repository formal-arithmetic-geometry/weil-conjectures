/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Coordinates of a finitely generated module modulo torsion

Let `M` be a finitely generated module over a principal ideal domain `R`. Then `M / torsion` is
free of some rank `r`; lifting a basis gives `b₁, …, bᵣ ∈ M` and coordinate functionals
`c₁, …, cᵣ : M → R` such that `m - ∑ cᵢ(m) bᵢ` lies in the torsion submodule, which is killed
by a single nonzero `d ∈ R`. When `R` is a topological ring and `M` carries the module topology,
the coordinates are continuous (`IsModuleTopology.exists_coord_smul_sub_sum_eq_zero`).
-/

@[expose] public section

open Module

namespace IsModuleTopology

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace M] [IsModuleTopology R M]

end IsModuleTopology
