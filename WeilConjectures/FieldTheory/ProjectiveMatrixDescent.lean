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

Source: Stacks Project, the construction preceding Theorem 03R7.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A locally constant matrix conjugation action descends to a central simple algebra.

For any vector v in that matrix space and a in L, the sum of g(a)T_g(v) over
Gamma is invariant, by reindexing the sum. If an L-linear functional kills all
these sums, linear independence of distinct field automorphisms implies it kills
every T_g(v), hence every v. Thus invariants span over L. Select an L-basis from
these invariant vectors. An invariant linear combination has coefficients fixed
by Gamma, hence in K; the selected vectors are therefore also a K-basis of A.
The explicit multiplication map L tensor_K A to the matrix algebra is now an
algebra isomorphism. In particular A is finite dimensional. A nonzero two-sided
ideal extends to a nonzero ideal of the simple matrix algebra and so to the whole
algebra. Extension of scalars preserves dimensions, forcing the ideal to equal A.
A central element extends to a scalar matrix, and invariance forces that scalar
into K. Thus the constructed A is central simple. Nonzero n ensures nontriviality.
Extend this multiplication isomorphism to Ksep to obtain e. Invariance says
b(g) * g(e(1 tensor a)) * b(g)^(-1) = e(1 tensor a); multiplying by the inverses
gives exactly the displayed descent equation. This also handles n = 1 and
unnormalized scalar lifts, without any division by the order of Gamma.

Source: Stacks Project, the construction preceding Theorem 03R7. -/
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
