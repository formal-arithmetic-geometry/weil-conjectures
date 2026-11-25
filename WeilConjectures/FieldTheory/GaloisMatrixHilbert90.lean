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
import WeilConjectures.FieldTheory.GaloisMatrixHilbert90Normalized

/-!
# Matrix Hilbert 90 over a separable closure

A locally constant cocycle `b : Gal(Kˢ/K) → GLₙ(Kˢ)` is a coboundary: there is `t ∈ GLₙ(Kˢ)`
with `b(g) g(t) = t` for all `g`.

## Implementation details

The cocycle descends to a finite Galois extension `L`, where the vectors `∑_g b(g) g(v)` are
invariant and span `L^n` by linear independence of characters; a basis of invariant vectors
gives `t`. The argument does not divide by the group order. The case `n ≠ 0` is
`Field.exists_galois_matrix_invariant_basis_normalized`.

## References

* Stacks Project, Tag 03R7, injectivity argument.
-/

@[expose] public section

universe u
namespace Field

/-- Matrix Hilbert 90: a locally constant cocycle `b : Gal(Kˢ/K) → GLₙ(Kˢ)` admits an invariant
matrix basis, i.e. some `t ∈ GLₙ(Kˢ)` with `b(g) g(t) = t` for all `g`. -/
theorem exists_galois_matrix_invariant_basis (K : Type u) [Field K] (n : ℕ)
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ t : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      ∀ g, b g * Matrix.GeneralLinearGroup.map g.toRingHom t = t := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_⟩
    intro g
    apply Subsingleton.elim
  · exact exists_galois_matrix_invariant_basis_normalized K n b hb hn hcoc

end Field
