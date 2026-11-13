/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Basic consequences of properness
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-- A proper morphism is separated, universally closed, of finite type, quasi-compact,
and quasi-separated. Over an affine base, its source is separated and quasi-compact. -/
theorem AlgebraicGeometry.proper_basic
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      QuasiSeparated f ∧ (IsAffine S → X.IsSeparated ∧ CompactSpace X) := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro hS
  let : IsAffine S := hS
  refine ⟨?_, QuasiCompact.compactSpace_of_compactSpace f⟩
  exact HasAffineProperty.iff_of_isAffine.mp (inferInstance : IsSeparated f)
