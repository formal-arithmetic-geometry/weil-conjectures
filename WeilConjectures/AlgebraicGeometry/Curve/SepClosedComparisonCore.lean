/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Blueprint statements

lemma-weil-pbc-curve-separably-closed-passage-core.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- Blueprint: lemma-weil-pbc-curve-separably-closed-passage-core. -/
theorem exists_sepClosed_comparison_core
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (K' : Type u) (_ : Field K') (_ : IsAlgClosed K')
      (D D' : Scheme.{u}) (b : D ⟶ Spec (.of K)) (b' : D' ⟶ Spec (.of K'))
      (j : Spec (.of K') ⟶ Spec (.of K)) (a : D' ⟶ D) (p : D ⟶ C) (p' : D' ⟶ C')
      (t : Spec (.of K) ⟶ Spec (.of k)),
      IsPullback p b f t ∧ IsPullback a b' b j ∧ IsUniversalHomeomorphism p ∧
        IsUniversalHomeomorphism p' ∧ p' ≫ ι' = a ≫ p := by
  sorry

end AlgebraicGeometry.IsCurve
