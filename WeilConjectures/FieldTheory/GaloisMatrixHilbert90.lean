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

Source: Stacks Project, Tag 03R7, injectivity argument, expanded as an invariant-basis proof of
the general-linear Hilbert 90 theorem.
-/

@[expose] public section

universe u
namespace Field

/-- A locally constant general-linear Galois cocycle admits an invariant matrix basis.

Source: Stacks Project, Tag 03R7, injectivity, general-linear descent argument. -/
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
