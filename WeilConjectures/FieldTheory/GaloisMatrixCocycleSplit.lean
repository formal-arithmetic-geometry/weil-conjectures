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

Source: Stacks Project, Tag 03R7, injectivity argument.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A genuine locally constant matrix descent cocycle makes a split form split over K.

Source: Stacks Project, Tag 03R7, injectivity via descent of vector spaces. -/
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
