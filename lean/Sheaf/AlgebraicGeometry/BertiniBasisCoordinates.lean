/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! Linear coordinate changes for the Bertini incidence equation. -/

@[expose] public section
set_option autoImplicit false
universe u v w w'
namespace Algebra
open MvPolynomial

private theorem extend_poly_equiv
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    {I : Type w} {J : Type w'} (e : MvPolynomial I k ≃ₐ[k] MvPolynomial J k) :
    ∃ eA : MvPolynomial I A ≃ₐ[A] MvPolynomial J A,
      ∀ p, eA (map (algebraMap k A) p) = map (algebraMap k A) (e p) := by
  have heC (t : k) : e (C t) = C t := e.commutes t
  have heCs (t : k) : e.symm (C t) = C t := e.symm.commutes t
  let F : MvPolynomial I A →ₐ[A] MvPolynomial J A :=
    aeval (fun i ↦ map (algebraMap k A) (e (X i)))
  let G : MvPolynomial J A →ₐ[A] MvPolynomial I A :=
    aeval (fun j ↦ map (algebraMap k A) (e.symm (X j)))
  have hF (p : MvPolynomial I k) :
      F (map (algebraMap k A) p) = map (algebraMap k A) (e p) := by
    have h : F.toRingHom.comp (map (algebraMap k A)) =
        (map (algebraMap k A)).comp e.toRingHom := by
      apply ringHom_ext
      · intro t
        simp [F, heC]
      · intro i
        simp [F]
    exact DFunLike.congr_fun h p
  have hG (p : MvPolynomial J k) :
      G (map (algebraMap k A) p) = map (algebraMap k A) (e.symm p) := by
    have h : G.toRingHom.comp (map (algebraMap k A)) =
        (map (algebraMap k A)).comp e.symm.toRingHom := by
      apply ringHom_ext
      · intro t
        simp [G, heCs]
      · intro j
        simp [G]
    exact DFunLike.congr_fun h p
  have hFG : F.comp G = AlgHom.id A (MvPolynomial J A) := by
    apply algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [show G (X j) = map (algebraMap k A) (e.symm (X j)) by simp [G],
      hF, e.apply_symm_apply, map_X]
  have hGF : G.comp F = AlgHom.id A (MvPolynomial I A) := by
    apply algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [show F (X i) = map (algebraMap k A) (e (X i)) by simp [F],
      hG, e.symm_apply_apply, map_X]
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF⟩

private theorem dual_coordinate_change_X
    (k : Type u) [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    {I : Type w} {J : Type w'} [Finite I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (b : Module.Basis I k V) (b' : Module.Basis J k V) (i : I) :
    ((SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.trans
      (SymmetricAlgebra.equivMvPolynomial b'.dualBasis)) (X i) =
      ∑ j, C (b.repr (b' j) i) * X j := by
  classical
  simp only [AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_symm_X]
  have h := congrArg (fun z ↦ SymmetricAlgebra.equivMvPolynomial b'.dualBasis
    (SymmetricAlgebra.ι k (Module.Dual k V) z)) (b'.dualBasis.sum_repr (b.dualBasis i))
  simp only [map_sum, map_smul, Module.Basis.dualBasis_repr,
    Module.Basis.dualBasis_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    Algebra.smul_def, map_mul, AlgEquiv.commutes] at h
  exact h.symm

/-- Changing the basis of a linear system changes the incidence equation by an invertible
linear change of coefficient variables, compatibly with extension of scalars.
Source: Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-basis-coordinates).

Proof: Identify both coefficient polynomial rings with the symmetric algebra of the dual
vector space. Its basis transition sends X_i to the sum of the new variables with
coefficients b_i^*(b'_j). Extend this isomorphism and its inverse to A by polynomial evaluation.
Expanding the old incidence equation, interchanging its two finite sums and using the basis
expansion of each b'_j gives the new equation. -/
theorem exists_bertiniBasisCoordinateChange
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    {V : Type v} [AddCommGroup V] [Module k V]
    {I : Type w} {J : Type w'} [Fintype I] [Fintype J]
    (b : Module.Basis I k V) (b' : Module.Basis J k V) (a : V →ₗ[k] A) :
    ∃ (e : MvPolynomial I k ≃ₐ[k] MvPolynomial J k)
      (eA : MvPolynomial I A ≃ₐ[A] MvPolynomial J A),
      (∀ p, eA (map (algebraMap k A) p) = map (algebraMap k A) (e p)) ∧
      eA (∑ i, C (a (b i)) * X i) = ∑ j, C (a (b' j)) * X j := by
  classical
  let e := (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.trans
    (SymmetricAlgebra.equivMvPolynomial b'.dualBasis)
  obtain ⟨eA, heA⟩ := extend_poly_equiv k A e
  refine ⟨e, eA, heA, ?_⟩
  have hX (i : I) : eA (X i) = ∑ j, C (algebraMap k A (b.repr (b' j) i)) * X j := by
    have h := heA (X i)
    dsimp only [e] at h
    simp only [map_X, dual_coordinate_change_X k b b', map_sum, map_mul, map_C] at h
    exact h
  have hC (t : A) : eA (C t) = C t := eA.commutes t
  simp only [map_sum, map_mul, hC, hX, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← mul_assoc, ← map_mul]
  rw [← Finset.sum_mul, ← map_sum]
  congr 2
  have h := congrArg a (b.sum_repr (b' j))
  rw [map_sum] at h
  simp only [a.map_smul, Algebra.smul_def] at h
  simpa only [mul_comm] using h

end Algebra
