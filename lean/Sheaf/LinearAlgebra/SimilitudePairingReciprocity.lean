/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Div
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Sheaf.Algebra.Polynomial.ReciprocalRootFactorization

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Reciprocity for a perfect pairing and a similitude pair

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-prop-reciprocity`,
`prop-duality-reciprocity.proof.md`, steps 1–2; Milne, Lectures on Etale Cohomology,
Chapter II, §27, proof of Theorem 27.12, p. 158
(blueprint: lem-weil-similitude-pairing-reciprocity).

The reciprocal-root multiset is the multiset of ordinary roots mapped by inversion.
Mathlib's `Polynomial.roots` retains multiplicities (`Polynomial.count_roots` identifies
its counts with `Polynomial.rootMultiplicity`). The explicit factor families use units.
-/

@[expose] public section

universe u v w t

open Polynomial

namespace LinearMap

/-- A perfect pairing scaled by a nonzero multiplier gives equal dimensions, invertible
endomorphisms, the determinant product, the transported dual action, polynomial reciprocity,
and reciprocal root and eigenvalue multisets over every algebraically closed extension.

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-prop-reciprocity`,
`prop-duality-reciprocity.proof.md`, steps 1–2; Milne, Lectures on Etale Cohomology,
Chapter II, §27, proof of Theorem 27.12, p. 158
(blueprint: lem-weil-similitude-pairing-reciprocity).

Proof plan (the eleven steps of the DAG node):
1. Choose a finite basis of V, using def-weil-finite-dimensional-subspace and
   def-weil-vector-space-dimension, and its coordinate dual basis.
2. Set J(w)(v) = p(v,w). Pull the dual basis back along the perfect-pairing equivalence
   to obtain a basis of W with the same cardinality, including dimension zero.
3. From the Leibniz formula (def-weil-pbc-matrix-determinant), compute det(1) = 1,
   det(sM) = s^n det(M), transpose invariance, and compatibility with ring maps.
4. In the paired bases the matrices A and B satisfy A.transpose * B = c * 1.
   Apply the square case of lem-weil-pbc-cauchy-binet and step 3 to obtain
   det(A) det(B) = c^n. Both determinants are nonzero.
5. The criterion in def-weil-endomorphism-determinant gives invertibility. Applying
   the similitude equation at (F inverse v, w) gives J G J inverse = c (F inverse).dualMap.
6. Expand det(1 - T M). Its constant coefficient is one and its coefficient of T^n
   is (-1)^n det(M); use step 4 to obtain both degrees and evaluations at zero
   (def-weil-reverse-characteristic-polynomial).
7. Over K[T], take determinants of A.transpose * (1 - T B) = A.transpose - c T.
   Steps 3 and 4 give det(F) P_G(T) = (-1)^n chi_F(c T), using the definitions of
   the characteristic and reverse characteristic polynomials.
8. A field homomorphism is injective. Apply lem-weil-coefficientwise-extension-degree
   and map step 7 to L[T], writing a = iota(det(F)) and b = iota(c), both nonzero.
9. Apply lem-weil-reciprocal-root-factorization to P_F. It supplies n unit factors
   and identifies their multiplicities; every other such family is a permutation.
10. Use lem-weil-reverse-charpoly-eq-reverse to obtain chi_F(U) = product(U - alpha).
    Comparing top coefficients gives product(alpha) = a. Step 8 becomes
    a P_G(T) = a product(1 - b alpha inverse T); cancel a.
11. Apply lem-weil-reciprocal-root-factorization to P_G to identify reciprocal roots
    as b/alpha with multiplicities (def-weil-root-multiplicity). Ordinary roots
    are (b z) inverse. Reversal for G similarly identifies its characteristic roots,
    hence eigenvalues, as b/alpha. Empty products give all assertions in dimension zero.
-/
theorem similitude_pairing_reciprocity
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (p : V →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (F : Module.End K V) (G : Module.End K W) (c : K)
    (hc : c ≠ 0) (hFG : ∀ (v : V) (w : W), p (F v) (G w) = c * p v w) :
    Module.finrank K W = Module.finrank K V ∧
      (Function.Bijective F ∧ Function.Bijective G ∧
        LinearMap.det F * LinearMap.det G = c ^ Module.finrank K V) ∧
      (F.charpolyRev.natDegree = Module.finrank K V ∧
        G.charpolyRev.natDegree = Module.finrank K V ∧
        F.charpolyRev.eval 0 = 1 ∧ G.charpolyRev.eval 0 = 1 ∧
        p.flip.toPerfPair.conj G = c • (Ring.inverse F).dualMap ∧
        C (LinearMap.det F) * G.charpolyRev =
          C ((-1 : K) ^ Module.finrank K V) * F.charpoly.comp (C c * X)) ∧
      (∀ (L : Type t) [Field L] [IsAlgClosed L] (ι : K →+* L),
        (G.charpolyRev.map ι).roots.map (fun z : L ↦ z⁻¹) =
          ((F.charpolyRev.map ι).roots.map (fun z : L ↦ z⁻¹)).map
            (fun α : L ↦ ι c / α) ∧
        (∀ α : Fin (Module.finrank K V) → Lˣ,
          F.charpolyRev.map ι = ∏ r, (1 - C (↑(α r) : L) * X) →
          G.charpolyRev.map ι = ∏ r, (1 - C (ι c * (↑(α r) : L)⁻¹) * X)) ∧
        (G.charpolyRev.map ι).roots =
          (F.charpolyRev.map ι).roots.map (fun z : L ↦ (ι c * z)⁻¹) ∧
        (G.charpoly.map ι).roots =
          (F.charpoly.map ι).roots.map (fun α : L ↦ ι c / α)) := by
  sorry

end LinearMap
