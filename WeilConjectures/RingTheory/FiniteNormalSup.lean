/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite suprema of finite integral intermediate algebras

The supremum of finitely many finite intermediate algebras in the integral closure is again
finite and contained in the integral closure.

## References

* [Stacks, Tag 0333]
-/

@[expose] public section

universe u v

/-- If the supremum of a finite family of finite intermediate algebras inside the integral
closure has integrally closed prime localizations, it is a finite intermediate algebra inside
the integral closure with integrally closed prime localizations. -/
theorem finite_normal_sup (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (s : Finset (Subalgebra A K)) (S : Subalgebra A K)
    (hS : S = s.sup (fun C : Subalgebra A K => C))
    (hs : ∀ C ∈ s, C ≤ integralClosure A K ∧ Module.Finite A C)
    (hn : ∀ (q : Ideal S) [q.IsPrime],
      IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  refine ⟨S, ?_, ?_, hn⟩
  · rw [hS]
    exact Finset.sup_le fun C hC ↦ (hs C hC).1
  · rw [hS]
    have hfinite : ∀ t : Finset (Subalgebra A K),
        (∀ C ∈ t, Module.Finite A C) → Module.Finite A (t.sup id : Subalgebra A K) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          intro _
          rw [Finset.sup_empty]
          infer_instance
      | @insert C t hC ih =>
          intro ht
          have : Module.Finite A C := ht C (Finset.mem_insert_self C t)
          have : Module.Finite A (t.sup id : Subalgebra A K) :=
            ih fun D hD ↦ ht D (Finset.mem_insert_of_mem hD)
          rw [Finset.sup_insert]
          exact Subalgebra.finite_sup C (t.sup id)
    exact hfinite s fun C hC ↦ (hs C hC).2
