/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.RingTheory.AdjoinRootCRTRootBlockAux

/-! # CRT block coordinates for multiplication by the root

Let `f` be monic whose reduction modulo `I` factors as a product `g * h` of coprime monic
polynomials. After reindexing and conjugation by a unit matrix over `A/I`, the reduced matrix of
multiplication by the root of `f` is block diagonal with the multiplication-by-root matrices of
`g` and `h`.

## References

* [Stacks Project, Tag 09XI]
-/

@[expose] public section

universe u

namespace Polynomial

/-- Let `f` be monic with `f mod I = g * h` for coprime monic `g`, `h`. Then there are an index
equivalence `d` and a unit matrix `U` over `A/I` conjugating the reindexed reduced matrix of
multiplication by the root of `f` into `fromBlocks Tg 0 0 Th`. -/
theorem adjoinRoot_crt_matrix_root_block
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) :
    let b := (AdjoinRoot.powerBasis' hf).basis
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f)
    let Tg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g)
    let Th := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis (AdjoinRoot.root h)
    ∃ (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree))
      (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d (T.map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks Tg 0 0 Th := by
  obtain ⟨d⟩ := adjoinRoot_crt_degree_equiv I f hf g h hg hh hfactor
  obtain ⟨U, hU⟩ := adjoinRoot_crt_matrix_for_degree_equiv I f hf g h hg hh hcoprime hfactor d
  exact ⟨d, U, hU⟩

end Polynomial
