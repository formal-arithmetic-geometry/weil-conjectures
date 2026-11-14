/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Curve.SepClosedComparisonCore
import WeilConjectures.AlgebraicGeometry.Curve.SepClosedComparisonCurve

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- A geometric comparison square over algebraically closed fields.
Source: Stacks Project, Tag 0A5E, proof (compatible algebraic closures). -/
theorem sepClosed_geometric_comparison
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (K' : Type u) (_ : Field K') (_ : IsAlgClosed K')
      (D D' : Scheme.{u}) (b : D ⟶ Spec (.of K)) (b' : D' ⟶ Spec (.of K'))
      (j : Spec (.of K') ⟶ Spec (.of K)) (a : D' ⟶ D) (p : D ⟶ C) (p' : D' ⟶ C'),
      IsCurve b ∧ IsProper b ∧ IsPullback a b' b j ∧
        IsUniversalHomeomorphism p ∧ IsUniversalHomeomorphism p' ∧ p' ≫ ι' = a ≫ p := by
  obtain ⟨K, hK, hKa, K', hK', hK'a, D, D', b, b', j, a, p, p', t, ht, hs, hp, hp', hcomm⟩ :=
    exists_sepClosed_comparison_core f h
  have : IsUniversalHomeomorphism p := hp
  obtain ⟨hb, hbp⟩ := isCurve_isProper_of_sepClosed_comparison_core f b p t ht
  exact ⟨K, hK, hKa, K', hK', hK'a, D, D', b, b', j, a, p, p', hb, hbp, hs, hp, hp', hcomm⟩

end AlgebraicGeometry.IsCurve
