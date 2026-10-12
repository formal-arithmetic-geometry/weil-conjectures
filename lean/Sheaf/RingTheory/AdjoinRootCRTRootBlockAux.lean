module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

universe u

namespace Polynomial

/-! Auxiliary CRT decomposition statements used by the root-block theorem.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux)
-/

/-- The degree indices of a monic CRT factorization can be identified.

Proof: degree additivity for monic products gives equal finite cardinalities, and
`Fintype.equivOfCardEq` supplies the equivalence.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux) -/
theorem adjoinRoot_crt_degree_equiv
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) :
    Nonempty (Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree)) := by
  have hdeg : f.natDegree = g.natDegree + h.natDegree := by
    rw [← hf.natDegree_map (Ideal.Quotient.mk I), hfactor,
      hg.natDegree_mul hh]
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp only [Fintype.card_fin, Fintype.card_sum, hdeg]

/-- For a chosen degree identification, CRT supplies the conjugating matrix.

Proof: apply the Chinese remainder algebra equivalence, concatenate the power
bases, and take the coordinate matrix of this equivalence; its inverse gives the
conjugation identity.
(blueprint: lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix) -/
theorem adjoinRoot_crt_matrix_for_degree_equiv
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic) (hcoprime : IsCoprime g h)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h)
    (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree)) :
    ∃ (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
        (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ),
      U.val * Matrix.reindex d d
          ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
            (AdjoinRoot.root f)).map (Ideal.Quotient.mk I)) * U⁻¹.val =
        Matrix.fromBlocks
          (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
            (AdjoinRoot.root g)) 0 0
          (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis
            (AdjoinRoot.root h)) := by
  sorry

end Polynomial
