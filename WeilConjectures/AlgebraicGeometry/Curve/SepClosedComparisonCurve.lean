/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- A base change of a proper curve whose projection is a universal homeomorphism
is a proper curve.
Source: Stacks Project, Tag 0A5E, the algebraic-closure base change in its proof. -/
theorem isCurve_isProper_of_sepClosed_comparison_core
    {k K : Type u} [Field k] [Field K] {C D : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    (b : D ⟶ Spec (.of K)) (p : D ⟶ C) [IsUniversalHomeomorphism p]
    (t : Spec (.of K) ⟶ Spec (.of k)) (h : IsPullback p b f t) :
    IsCurve b ∧ IsProper b := by
  have : IsProper b := MorphismProperty.of_isPullback h inferInstance
  refine ⟨⟨?_⟩, inferInstance⟩
  rw [p.isHomeomorph.topologicalKrullDim_eq]
  exact IsCurve.krullDim_le_one (f := f)

end AlgebraicGeometry.IsCurve
