/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Blueprint statements

lemma-weil-pbc-curve-separably-closed-passage-curve.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- Blueprint: lemma-weil-pbc-curve-separably-closed-passage-curve. -/
theorem isCurve_isProper_of_sepClosed_comparison_core
    {k K : Type u} [Field k] [Field K] {C D : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    (b : D ⟶ Spec (.of K)) (p : D ⟶ C) [IsUniversalHomeomorphism p]
    (t : Spec (.of K) ⟶ Spec (.of k)) (h : IsPullback p b f t) :
    IsCurve b ∧ IsProper b := by
  sorry

end AlgebraicGeometry.IsCurve
