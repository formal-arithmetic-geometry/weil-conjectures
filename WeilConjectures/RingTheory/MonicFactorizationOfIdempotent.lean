/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Group.Idempotent
import WeilConjectures.LinearAlgebra.IdempotentCharpolyMonic
import WeilConjectures.LinearAlgebra.IdempotentCharpolyMulComplement
import WeilConjectures.RingTheory.AdjoinRootIdempotentCharpolyMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic.NoncommRing

/-!
# Monic factorization from a lifted idempotent

An idempotent of `A[X]/(f)` lifting the Chinese remainder idempotent of a coprime factorization
`f ≡ g₀ h₀` modulo `I` gives a monic factorization `f = g h` lifting `g₀ h₀`.

## Implementation details

With `T` the matrix of multiplication by `X` and `P` that of the idempotent `e` in the power
basis, `g` and `h` are `Matrix.idempotentCharpoly T P` and `Matrix.idempotentCharpoly T (1 - P)`.
They are monic by the constant-rank argument over a Jacobson ideal, and `g h` is the
characteristic polynomial of `T`, which is `f`.

## References

* [Stacks, Tag 09XI] (proof of (3) implies (1))
-/

@[expose] public section

universe u

namespace Polynomial

/-- An idempotent of `A[X]/(f)` lifting the Chinese remainder element `(1, 0)` yields a monic
factorization lifting `g₀ * h₀`. The two `AdjoinRoot.map` conditions are precisely its residues
in the Chinese remainder factors, so they express that its reduction is the specified idempotent
of `B/IB`. -/
theorem exists_monic_factorization_of_idempotent
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (e : AdjoinRoot f) (he : IsIdempotentElem e)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g₀
      (hfactor.symm ▸ dvd_mul_right g₀ h₀) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h₀
      (hfactor.symm ▸ dvd_mul_left h₀ g₀) e = 0) :
    ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ := by
  classical
  let b := (AdjoinRoot.powerBasis' hf).basis
  let T := Algebra.leftMulMatrix b (AdjoinRoot.root f)
  let P := Algebra.leftMulMatrix b e
  have hP : P * P = P := by
    dsimp [P]
    rw [← map_mul, he.eq]
  have hTP : T * P = P * T := by
    dsimp [T, P]
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  have hTQ : T * (1 - P) = (1 - P) * T := by
    noncomm_ring [hTP]
  obtain ⟨hgmap, hhmap⟩ := adjoinRoot_idempotentCharpoly_map
    I f hf g₀ h₀ hg₀ hh₀ hcoprime hfactor e he₁ he₀
  have hg : (Matrix.idempotentCharpoly T P).Monic :=
    Matrix.idempotentCharpoly_monic_of_map_monic I hI T P hP hTP (hgmap ▸ hg₀)
  have hh : (Matrix.idempotentCharpoly T (1 - P)).Monic :=
    Matrix.idempotentCharpoly_monic_of_map_monic I hI T (1 - P) hQ hTQ (hhmap ▸ hh₀)
  have hchar : T.charpoly = f := by
    nontriviality A
    have hmin : f = minpoly A (AdjoinRoot.root f) := by
      apply minpoly.unique' A (AdjoinRoot.root f) hf
      · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      · intro q hq
        by_cases hzero : q = 0
        · exact Or.inl hzero
        · right
          intro hroot
          have hdeg := (AdjoinRoot.powerBasis' hf).dim_le_degree_of_root hzero hroot
          exact (not_le_of_gt hq) ((degree_eq_natDegree hf.ne_zero).symm ▸ hdeg)
    exact (charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hf)).trans hmin.symm
  refine ⟨Matrix.idempotentCharpoly T P, Matrix.idempotentCharpoly T (1 - P),
    hg, hh, ?_, hgmap, hhmap⟩
  exact hchar.symm.trans (Matrix.idempotentCharpoly_mul_complement T P hP hTP).symm

end Polynomial
