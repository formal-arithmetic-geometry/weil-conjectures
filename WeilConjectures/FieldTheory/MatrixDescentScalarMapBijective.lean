/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.MatrixDescentInvariants
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.MatrixDescentInvariantsSpan
import WeilConjectures.FieldTheory.MatrixDescentInvariantsLinearIndependent
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of twisted Galois invariants

Source: Stacks Project, Lemma 03R6, preceding Theorem 03R7.
-/

@[expose] public section

universe u

namespace Field

/-- Scalar extension of the explicitly constructed invariant algebra is bijective.

Source: Stacks Project, construction preceding Theorem 03R7. -/
theorem matrixDescentScalarMap_bijective (K : Type u) [Field K]
    (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M)
    (hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val) :
    Function.Bijective (matrixDescentScalarMap K n b) := by
  classical
  let A := matrixDescentInvariants K n b
  let c := Module.Free.chooseBasis K A
  let f := (matrixDescentScalarMap K n b).toLinearMap
  have hf (i) : f (c.baseChange (SeparableClosure K) i) =
      (c i : Matrix (Fin n) (Fin n) (SeparableClosure K)) := by
    rw [Module.Basis.baseChange_apply]
    exact matrixDescentScalarMap_one_tmul K n b (c i)
  have hli : LinearIndependent (SeparableClosure K)
      (f ∘ (c.baseChange (SeparableClosure K))) := by
    simpa only [Function.comp_def, hf] using
      matrixDescentInvariants_linearIndependent K n b c c.linearIndependent
  have hspan : Submodule.span (SeparableClosure K)
      (Set.range (f ∘ (c.baseChange (SeparableClosure K)))) = ⊤ := by
    have hc : Submodule.span K
        (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) =
        A.toSubmodule := by
      calc
        _ = (Submodule.span K (Set.range c)).map A.toSubmodule.subtype := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
        _ = A.toSubmodule := by rw [c.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hrange : Submodule.span (SeparableClosure K)
        (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) =
        Submodule.span (SeparableClosure K)
          (Set.range fun a : A ↦ (a : Matrix (Fin n) (Fin n) (SeparableClosure K))) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨c i, rfl⟩
      · apply Submodule.span_le.mpr
        rintro _ ⟨a, rfl⟩
        have ha : (a : Matrix (Fin n) (Fin n) (SeparableClosure K)) ∈
            Submodule.span K
              (Set.range fun i ↦ (c i : Matrix (Fin n) (Fin n) (SeparableClosure K))) := by
          rw [hc]
          exact a.property
        exact Submodule.span_le_restrictScalars K (SeparableClosure K) _ ha
    simpa only [Function.comp_def, hf] using
      hrange.trans (matrixDescentInvariants_span K n b hb h1 hm)
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top
    (c.baseChange (SeparableClosure K)).span_eq hli hspan

end Field
