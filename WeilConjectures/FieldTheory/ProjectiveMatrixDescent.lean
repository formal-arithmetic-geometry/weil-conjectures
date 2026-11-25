/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic

import WeilConjectures.FieldTheory.MatrixDescentScalarMapBijective
import WeilConjectures.FieldTheory.MatrixFormCentralSimple

/-!
# Descent of a locally constant projective matrix action

A locally constant family `b` of invertible matrices over `Kˢᵉᵖ`, indexed by `Gal(Kˢᵉᵖ/K)` and
satisfying the cocycle conditions for the conjugation action, descends to a central simple
`K`-algebra `A` with `Kˢᵉᵖ ⊗[K] A ≅ Mₙ(Kˢᵉᵖ)` compatibly with the twisted Galois action.

## Implementation details

`A` is constructed explicitly as the subalgebra of matrices fixed by the twisted action
`T_g(M) = b(g) * g(M) * b(g)⁻¹`. By local constancy, `b` factors through a finite Galois
quotient `Gal(L/K)`, and `A` is the invariant subalgebra of `Mₙ(L)`. Averaging sums
`∑ g(a) T_g(v)` together with linear independence of characters show that the invariants span
over `L`, so the multiplication map `L ⊗[K] A → Mₙ(L)` is an isomorphism; this makes `A`
central simple. The argument needs no division by the order of the Galois group and also
covers `n = 1` and unnormalized scalar lifts.

## References

* Stacks Project, the construction preceding Theorem 03R7
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A locally constant matrix conjugation action descends to a central simple algebra: there
are a central simple `K`-algebra `A` and an isomorphism `e : Kˢᵉᵖ ⊗[K] A ≃ Mₙ(Kˢᵉᵖ)` with
`g(e(1 ⊗ a)) = b(g)⁻¹ * e(1 ⊗ a) * b(g)` for all `g` and `a`. -/
theorem exists_CSA_of_matrix_descent_action (K : Type u) [Field K]
    (n : ℕ) (hn : n ≠ 0)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M)
    (hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val) :
    ∃ (A : CSA.{u, u} K)
      (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K)),
      ∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val := by
  classical
  let S := matrixDescentInvariants K n b
  let e := AlgEquiv.ofBijective (matrixDescentScalarMap K n b)
    (matrixDescentScalarMap_bijective K n b hb h1 hm)
  obtain ⟨hcentral, hsimple, hfinite⟩ := centralSimple_of_matrix_form K
    (SeparableClosure K) S n hn e
  let A : CSA.{u, u} K :=
    { toAlgCat := AlgCat.of K S
      isCentral := hcentral
      isSimple := hsimple
      fin_dim := hfinite }
  refine ⟨A, e, ?_⟩
  intro g a
  change ((matrixDescentScalarMap K n b) (1 ⊗ₜ[K] a)).map g =
    ((b g)⁻¹).val * (matrixDescentScalarMap K n b) (1 ⊗ₜ[K] a) * (b g).val
  rw [matrixDescentScalarMap_one_tmul]
  have ha := a.property g
  have h := congrArg (fun M ↦ ((b g)⁻¹).val * M * (b g).val) ha
  simpa [mul_assoc] using h

end Field
