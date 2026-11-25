/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.FieldTheory.CentralSimpleTensorEnd
import WeilConjectures.FieldTheory.BrauerScalarDefectTensorSplit

/-!
# Equal scalar-defect classes imply Brauer equivalence

If two central simple algebras `A` and `B` over `K` have the same scalar-defect class in
`GaloisUnitsH2 K`, then they are Brauer equivalent.

## Implementation details

Equality in cohomology makes the tensor product of `A` with the opposite of `B` split, via
matrix Hilbert 90 on a finite Galois extension. The isomorphism `Bᵐᵒᵖ ⊗ B ≅ M_m(K)`
then gives `M_m(A) ≅ A ⊗ (Bᵐᵒᵖ ⊗ B) ≅ (A ⊗ Bᵐᵒᵖ) ⊗ B ≅ M_n(B)`.

## References

* Stacks Project, Theorem 03R7 (injectivity) and Section 0DVG.
-/

@[expose] public section
universe u
namespace Field
/-- Central simple algebras `A` and `B` with equal scalar-defect classes are Brauer
equivalent. -/
theorem brauerEquivalent_of_brauerScalarDefect_eq (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : x = y) : IsBrauerEquivalent A B := by
  classical
  obtain ⟨n, hn, ⟨eAB⟩⟩ := tensor_opposite_split_of_brauerScalarDefect_eq K A B x y hx hy h
  let m := Module.finrank K B
  have hm : m ≠ 0 := ne_of_gt (Module.finrank_pos (R := K) (M := B))
  let eBB : (TensorProduct K Bᵐᵒᵖ B) ≃ₐ[K] Matrix (Fin m) (Fin m) K :=
    (Algebra.TensorProduct.comm K Bᵐᵒᵖ B).trans
      ((AlgEquiv.ofBijective (AlgHom.mulLeftRight K B)
        (centralSimple_mulLeftRight_bijective K B)).trans
        (LinearMap.toMatrixAlgEquiv (Module.finBasis K B)))
  -- M_m(A) ≃ A ⊗ (Bᵐᵒᵖ ⊗ B) ≃ (A ⊗ Bᵐᵒᵖ) ⊗ B ≃ M_n(B).
  refine ⟨m, n, hm, hn, ⟨?_⟩⟩
  exact (matrixEquivTensor (Fin m) K A).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A) eBB.symm).trans
      ((Algebra.TensorProduct.assoc K K K A Bᵐᵒᵖ B).symm.trans
        ((Algebra.TensorProduct.congr eAB (AlgEquiv.refl : B ≃ₐ[K] B)).trans
          ((Algebra.TensorProduct.comm K (Matrix (Fin n) (Fin n) K) B).trans
            (matrixEquivTensor (Fin n) K B).symm))))
end Field
