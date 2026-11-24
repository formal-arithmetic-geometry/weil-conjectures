/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.GaloisInvariantVectorsSpan
import WeilConjectures.FieldTheory.SpanningSetUnitMatrix

/-! # Matrix Hilbert 90 for locally constant cocycles

A locally constant cocycle `b` of the absolute Galois group with values in `GL_n(K^sep)`,
`n ≠ 0`, is trivial: there is `t ∈ GL_n(K^sep)` with `b_g g(t) = t` for all `g`.

## Implementation details

The columns of `t` are taken from the `b`-twisted Galois invariant vectors, which span
`(K^sep)ⁿ` by `galois_invariant_vectors_span`: summing the twisted Galois translates of a
vector over a finite Galois quotient gives invariant vectors, and linear independence of field
automorphisms shows that they span. -/
@[expose] public section
universe u
namespace Field
/-- Matrix Hilbert 90 in positive dimension: for a locally constant cocycle `b` with values in
`GL_n(K^sep)`, `n ≠ 0`, there is `t ∈ GL_n(K^sep)` with `b_g g(t) = t` for all `g`. -/
theorem exists_galois_matrix_invariant_basis_normalized (K : Type u) [Field K] (n : ℕ)
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hn : n ≠ 0)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ t : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      ∀ g, b g * Matrix.GeneralLinearGroup.map g.toRingHom t = t := by
  have _hn := hn
  obtain ⟨t, ht⟩ := Matrix.exists_unit_matrix_columns_mem (SeparableClosure K) n
    {v | ∀ g, (b g).val.mulVec (g ∘ v) = v} (galois_invariant_vectors_span K n b hb hcoc)
  refine ⟨t, ?_⟩
  intro g
  apply Units.ext
  funext i j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (ht j g) i
end Field
