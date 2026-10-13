/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Simultaneous CRT coordinates for multiplication matrices

Let `f ∈ A[X]` be monic and suppose its reduction modulo an ideal `I` factors as a product
`g * h` of coprime monic polynomials over `A ⧸ I`. In the power bases, multiplication by the root
of `AdjoinRoot f` and by an idempotent lifting `(1, 0)` become, after a common change of basis
over `A ⧸ I`, block diagonal with blocks the root multiplication matrices of `g`, `h` and the
blocks `1`, `0` (Stacks, Tag 09XI, proof of (3) implies (1)).
-/

@[expose] public section

universe u

open Polynomial

namespace Polynomial

/-! Auxiliary CRT decomposition statements used by the root-block theorem.
-/

/-- The degree indices of a monic CRT factorization can be identified. -/
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

/-- In the power basis, multiplication by the root is computed by monic remainders. -/
private theorem root_matrix_entry {R : Type*} [CommRing R]
    (p : R[X]) (hp : p.Monic) (i j : Fin p.natDegree) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis (AdjoinRoot.root p) i j =
      (X ^ (j.val + 1) %ₘ p).coeff i.val := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (AdjoinRoot.powerBasisAux' hp).repr
    (AdjoinRoot.root p * (AdjoinRoot.powerBasis' hp).basis j) i = _
  rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow]
  change (AdjoinRoot.powerBasisAux' hp).repr
    (AdjoinRoot.root p * AdjoinRoot.root p ^ j.val) i = _
  rw [← pow_succ']
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]

/-- For a chosen degree identification, CRT supplies the conjugating matrix. -/
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
  classical
  let R := A ⧸ I
  let p := f.map (Ideal.Quotient.mk I)
  let J : Ideal R[X] := Ideal.span {g}
  let K : Ideal R[X] := Ideal.span {h}
  have hJK : IsCoprime J K := (Ideal.isCoprime_span_singleton_iff g h).mpr hcoprime
  have hpJK : Ideal.span {p} = J * K := by
    change Ideal.span {p} = Ideal.span {g} * Ideal.span {h}
    rw [Ideal.span_singleton_mul_span_singleton]
    exact congrArg (fun q ↦ Ideal.span {q}) hfactor
  let E : AdjoinRoot p ≃+* AdjoinRoot g × AdjoinRoot h :=
    (Ideal.quotEquivOfEq hpJK).trans (Ideal.quotientMulEquivQuotientProd J K hJK)
  have hE (q : R[X]) : E (AdjoinRoot.mk p q) =
      (AdjoinRoot.mk g q, AdjoinRoot.mk h q) := by
    change ((Ideal.quotientMulEquivQuotientProd J K hJK)
      ((Ideal.quotEquivOfEq hpJK) (Ideal.Quotient.mk _ q))) = _
    rw [Ideal.quotEquivOfEq_mk]
    apply Prod.ext
    · rw [Ideal.quotientMulEquivQuotientProd_fst]
      rfl
    · rw [Ideal.quotientMulEquivQuotientProd_snd]
      rfl
  let e : AdjoinRoot p ≃ₐ[R] AdjoinRoot g × AdjoinRoot h :=
    AlgEquiv.ofRingEquiv (f := E) (fun a ↦ by
      change E (AdjoinRoot.mk p (C a)) =
        (AdjoinRoot.mk g (C a), AdjoinRoot.mk h (C a))
      exact hE (C a))
  have he : e (AdjoinRoot.root p) = (AdjoinRoot.root g, AdjoinRoot.root h) := hE X
  have hp : p.Monic := hf.map (Ideal.Quotient.mk I)
  let c : Fin p.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree) :=
    (finCongr (hf.natDegree_map (Ideal.Quotient.mk I))).trans d
  let b := (AdjoinRoot.powerBasis' hp).basis.reindex c
  let b' := (AdjoinRoot.powerBasis' hg).basis.prod (AdjoinRoot.powerBasis' hh).basis
  have hM : Algebra.leftMulMatrix b (AdjoinRoot.root p) =
      Matrix.reindex d d
        ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
          (AdjoinRoot.root f)).map (Ideal.Quotient.mk I)) := by
    ext i j
    simp only [b, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← Algebra.leftMulMatrix_eq_repr_mul, root_matrix_entry,
      ← Algebra.leftMulMatrix_eq_repr_mul, root_matrix_entry]
    change (X ^ ((d.symm j).val + 1) %ₘ p).coeff (d.symm i).val = _
    rw [← coeff_map, map_modByMonic _ hf, Polynomial.map_pow, Polynomial.map_X]
  let U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
      (Fin g.natDegree ⊕ Fin h.natDegree) R)ˣ :=
    { val := LinearMap.toMatrix b b' e.toLinearMap
      inv := LinearMap.toMatrix b' b e.symm.toLinearMap
      val_inv := by
        rw [← LinearMap.toMatrix_comp b' b b']
        simp [LinearMap.toMatrix_id]
      inv_val := by
        rw [← LinearMap.toMatrix_comp b b' b]
        simp [LinearMap.toMatrix_id] }
  refine ⟨U, ?_⟩
  rw [← hM]
  change LinearMap.toMatrix b b' e.toLinearMap *
      Algebra.leftMulMatrix b (AdjoinRoot.root p) *
      LinearMap.toMatrix b' b e.symm.toLinearMap = _
  rw [Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_comp b b b',
    ← LinearMap.toMatrix_comp b' b b']
  have hconj :
      (e.toLinearMap.comp (Algebra.lmul R (AdjoinRoot p) (AdjoinRoot.root p))).comp
        e.symm.toLinearMap =
      (Algebra.lmul R (AdjoinRoot g) (AdjoinRoot.root g)).prodMap
        (Algebra.lmul R (AdjoinRoot h) (AdjoinRoot.root h)) := by
    apply LinearMap.ext
    intro x
    change e (AdjoinRoot.root p * e.symm x) =
      (AdjoinRoot.root g * x.1, AdjoinRoot.root h * x.2)
    rw [map_mul, he, e.apply_symm_apply]
    rfl
  rw [hconj]
  exact LinearMap.toMatrix_prodMap (AdjoinRoot.powerBasis' hg).basis
    (AdjoinRoot.powerBasis' hh).basis _ _

/-- Root multiplication has CRT block coordinates after coefficient reduction.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1), the decomposition of B/IB. -/
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

/-- Any coordinates putting the root matrix into CRT blocks put a prescribed CRT
lift into the corresponding projection blocks.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1), the decomposition of B/IB. -/
theorem adjoinRoot_crt_matrix_lift_block
    {A : Type u} [CommRing A] (I : Ideal A) [Nontrivial (A ⧸ I)]
    (f : A[X]) (hf : f.Monic) (g h : (A ⧸ I)[X])
    (hg : g.Monic) (hh : h.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g * h) (e : AdjoinRoot f)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g (hfactor.symm ▸ dvd_mul_right g h) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h (hfactor.symm ▸ dvd_mul_left h g) e = 0)
    (d : Fin f.natDegree ≃ (Fin g.natDegree ⊕ Fin h.natDegree))
    (U : (Matrix (Fin g.natDegree ⊕ Fin h.natDegree)
      (Fin g.natDegree ⊕ Fin h.natDegree) (A ⧸ I))ˣ)
    (hT : U.val * Matrix.reindex d d
      ((Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
        (AdjoinRoot.root f)).map (Ideal.Quotient.mk I)) * U⁻¹.val =
      Matrix.fromBlocks
        (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis (AdjoinRoot.root g))
        0 0 (Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis (AdjoinRoot.root h))) :
    let b := (AdjoinRoot.powerBasis' hf).basis
    let P := Algebra.leftMulMatrix b e
    U.val * Matrix.reindex d d (P.map (Ideal.Quotient.mk I)) * U⁻¹.val =
      Matrix.fromBlocks 1 0 0 0 := by
  classical
  let R := A ⧸ I
  let N := Fin g.natDegree ⊕ Fin h.natDegree
  let L := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hf).basis
  let Lg := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hg).basis
  let Lh := Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hh).basis
  let qg := AdjoinRoot.map (Ideal.Quotient.mk I) f g
    (hfactor.symm ▸ dvd_mul_right g h)
  let qh := AdjoinRoot.map (Ideal.Quotient.mk I) f h
    (hfactor.symm ▸ dvd_mul_left h g)
  let H : AdjoinRoot f →+* Matrix N N R :=
    (Matrix.reindexRingEquiv R d).toRingHom.comp
      ((Ideal.Quotient.mk I).mapMatrix.comp L.toRingHom)
  let C : Matrix N N R →+* Matrix N N R :=
    { toFun := fun M ↦ U.val * M * U⁻¹.val
      map_zero' := by simp
      map_one' := by simp
      map_add' := by intros; simp [mul_add, add_mul]
      map_mul' := by
        intro M M'
        simp only [mul_assoc]
        simp only [Units.inv_mul_cancel_left] }
  let F := C.comp H
  let G : AdjoinRoot f →+* Matrix N N R :=
    { toFun := fun x ↦ Matrix.fromBlocks (Lg (qg x)) 0 0 (Lh (qh x))
      map_zero' := by simp
      map_one' := by simp [Matrix.fromBlocks_one]
      map_add' := by
        intro x y
        dsimp [N, R]
        simp only [map_add]
        rw [Matrix.fromBlocks_add]
        simp
      map_mul' := by
        intro x y
        dsimp [N, R]
        simp only [map_mul]
        rw [Matrix.fromBlocks_multiply]
        simp }
  have hFG : F = G := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change U.val * Matrix.reindex d d ((L (AdjoinRoot.of f a)).map
        (Ideal.Quotient.mk I)) * U⁻¹.val =
          Matrix.fromBlocks (Lg (qg (AdjoinRoot.of f a))) 0 0
            (Lh (qh (AdjoinRoot.of f a)))
      have hL : L (AdjoinRoot.of f a) = a • 1 := by
        rw [← AdjoinRoot.algebraMap_eq f, L.commutes, Algebra.algebraMap_eq_smul_one]
      have hmap : Matrix.reindex d d ((a • (1 : Matrix (Fin f.natDegree)
          (Fin f.natDegree) A)).map (Ideal.Quotient.mk I)) =
          (Ideal.Quotient.mk I a) • (1 : Matrix N N R) := by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.reindex_apply, Matrix.map_apply, hij]
      have hLg : Lg (qg (AdjoinRoot.of f a)) = (Ideal.Quotient.mk I a) • 1 := by
        simp only [qg, AdjoinRoot.map_of]
        rw [← AdjoinRoot.algebraMap_eq g, Lg.commutes, Algebra.algebraMap_eq_smul_one]
      have hLh : Lh (qh (AdjoinRoot.of f a)) = (Ideal.Quotient.mk I a) • 1 := by
        simp only [qh, AdjoinRoot.map_of]
        rw [← AdjoinRoot.algebraMap_eq h, Lh.commutes, Algebra.algebraMap_eq_smul_one]
      have hb : Matrix.fromBlocks ((Ideal.Quotient.mk I a) •
          (1 : Matrix (Fin g.natDegree) (Fin g.natDegree) R)) 0 0
          ((Ideal.Quotient.mk I a) •
          (1 : Matrix (Fin h.natDegree) (Fin h.natDegree) R)) =
          (Ideal.Quotient.mk I a) • (1 : Matrix N N R) := by
        simpa only [smul_zero, Matrix.fromBlocks_one] using
          (Matrix.fromBlocks_smul (Ideal.Quotient.mk I a)
            (1 : Matrix (Fin g.natDegree) (Fin g.natDegree) R) 0 0
            (1 : Matrix (Fin h.natDegree) (Fin h.natDegree) R)).symm
      rw [hL, hmap, hLg, hLh, hb]
      simp
    · change U.val * Matrix.reindex d d ((L (AdjoinRoot.root f)).map
        (Ideal.Quotient.mk I)) * U⁻¹.val =
          Matrix.fromBlocks (Lg (qg (AdjoinRoot.root f))) 0 0
            (Lh (qh (AdjoinRoot.root f)))
      simpa [L, Lg, Lh, qg, qh] using hT
  have hx := RingHom.congr_fun hFG e
  change U.val * Matrix.reindex d d ((L e).map (Ideal.Quotient.mk I)) * U⁻¹.val =
    Matrix.fromBlocks (Lg (qg e)) 0 0 (Lh (qh e)) at hx
  simpa [L, Lg, Lh, qg, qh, he₁, he₀] using hx

/-- Coefficient reduction and Chinese remainders simultaneously put multiplication
by the root and by a CRT lift in block coordinates.
Source: Stacks Project, Tag 09XI, proof of (3) implies (1), the decomposition of B/IB.
(blueprint: `lem-weil-pbc-adjoinRoot-crt-matrix`) -/
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
