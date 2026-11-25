/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.GaloisMatrixCocycleDescent

/-!
# Splitting an algebra with a genuine matrix descent cocycle

A `K`-algebra `D` that becomes a matrix algebra over the separable closure, with a genuine
locally constant matrix descent cocycle, is already a matrix algebra over `K`.

## Implementation details

The cocycle descends to a finite Galois extension, where matrix Hilbert 90 is proved without
dividing by the group order, using the vectors `∑_g b(g) g(v)` and linear independence of
characters. Conjugating by the resulting matrix makes the descent datum trivial, so the
equivalence restricts to `D ≃ M_n(K)`. No central simplicity is used, and `n = 0` is allowed.

## References

* Stacks Project, Tag 03R7 (injectivity argument) and Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A genuine locally constant matrix descent cocycle makes a split form split over `K`: if
`e : Ksep ⊗ D ≅ M_n(Ksep)` has descent datum given by a locally constant cocycle `b` with values
in `GL_n(Ksep)`, then `D ≅ M_n(K)`. -/
theorem nonempty_algEquiv_matrix_of_galois_cocycle (K : Type u) [Field K]
    (D : Type u) [Ring D] [Algebra K D] (n : ℕ)
    (e : (SeparableClosure K ⊗[K] D) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : Gal(SeparableClosure K/K)) (a : D),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    Nonempty (D ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf⟩ := exists_algHom_matrix_of_galois_cocycle K D n e b hb hdesc hcoc
  have hfbij : Function.Bijective f := hf
  have ef : D ≃ₐ[K] Matrix (Fin n) (Fin n) K := AlgEquiv.ofBijective f hfbij
  exact ⟨ef⟩

end Field
