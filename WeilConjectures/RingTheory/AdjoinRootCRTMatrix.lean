/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.Coprime.Basic

import WeilConjectures.RingTheory.AdjoinRootCRTRootBlock
import WeilConjectures.RingTheory.AdjoinRootCRTLiftBlock

/-! # Simultaneous CRT coordinates for multiplication matrices

Let `f` be monic whose reduction modulo `I` factors as a product `g * h` of coprime monic
polynomials. There are coordinates over `A/I` in which multiplication by the root of `f` is block
diagonal with the multiplication-by-root matrices of `g` and `h`, and multiplication by a CRT lift
`e` is `diag(1, 0)`.

## References

* [Stacks Project, Tag 09XI]
-/

@[expose] public section

universe u

namespace Polynomial

/-- Let `f` be monic with `f mod I = g * h` for coprime monic `g`, `h`, and let `e ∈ A[X]/(f)`
map to `1` in `(A/I)[X]/(g)` and to `0` in `(A/I)[X]/(h)`. Then there are an index equivalence
`d` and a unit matrix `U` over `A/I` conjugating the reduced matrix of multiplication by the root
into `fromBlocks Tg 0 0 Th`, and the reduced matrix of multiplication by `e` into
`fromBlocks 1 0 0 0`. -/
theorem adjoinRoot_crt_matrix
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h)
    (e : AdjoinRoot f)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g
      (hfactor.symm ▸ dvd_mul_right g h) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h
      (hfactor.symm ▸ dvd_mul_left h g) e = 0) :
    let b := (AdjoinRoot.powerBasis' hf).basis;
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f);
    let P := Algebra.leftMulMatrix b e;
    let Tg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g);
    let Th := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis (AdjoinRoot.root h);
    ∃ (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree))
      (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d (T.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks Tg 0 0 Th ∧
      U.val * Matrix.reindex d d (P.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks 1 0 0 0 := by
  classical
  dsimp
  obtain ⟨d, U, hT⟩ := adjoinRoot_crt_matrix_root_block I f hf g h hg hh hcoprime hfactor
  refine ⟨d, U, hT, ?_⟩
  exact adjoinRoot_crt_matrix_lift_block I f hf g h hg hh hfactor e he₁ he₀ d U hT

end Polynomial
