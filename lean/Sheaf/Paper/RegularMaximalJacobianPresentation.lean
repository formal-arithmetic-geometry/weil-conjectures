/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.Paper.MaximalIdealDifferentialCotangentDimension
import Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective

/-!
# Invertible Jacobian presentations near regular closed points

Source: Stacks Project, Algebra, proof of Lemma 00TS and proof of Lemma 00TE.
(blueprint: lem-weil-pbc-regular-maximal-jacobian-presentation).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A regular closed point has a principal neighbourhood with an explicit polynomial
presentation and an invertible Jacobian minor. This statement concerns equations and
an algebra isomorphism; it does not assert smoothness.
Source: Stacks Project, Algebra, proof of Lemma 00TS, implication (1) => (4),
and the inverse-variable construction in the proof of Lemma 00TE.
(blueprint: lem-weil-pbc-regular-maximal-jacobian-presentation).

Proof:
1. Take a finite polynomial presentation phi : P -> S with kernel I. The inverse
   image M of m is maximal. The localization A=P_M is regular, and A/IA is
   isomorphic to the regular local ring S_m. The proved regular-local quotient
   independent-generators theorem (00NR) gives finitely many generators of IA
   whose classes are independent in the cotangent space of A.
2. Clear denominators to obtain equations f_j in I. Scaling each cotangent class
   by its nonzero denominator preserves independence. The closed-point cotangent
   comparison identifies the cotangent dimension of A with the differential fibre
   dimension. The conormal map is surjective, since the residue field is k and its
   differentials vanish; equality of these finite dimensions makes it an isomorphism.
   In the polynomial differential basis its matrix columns are the gradients of f_j
   evaluated in the residue field. Their independence therefore gives a nonzero
   square minor Delta of size the number of equations. Its image under phi avoids m.
3. Put J=(f_j). The quotient map P/J -> S becomes an isomorphism at M since JA=IA.
   The module I/J is finite over the Noetherian ring P. Choose its finite generators.
   Each generator vanishes at M, so some element outside M annihilates it. The product
   b of these elements annihilates I/J, giving P_b/JP_b isomorphic to S_(phi(b)).
4. Set g=phi(b)*phi(Delta), outside m. Present S_g by adjoining inverse variables
   z,w to P, with equations f_j, bz-1, Delta*w-1. Select the old variables giving
   Delta, together with z and w. The enlarged Jacobian block is triangular with
   diagonal blocks the old minor, b and Delta. Its determinant is b*Delta^2, a unit
   in this quotient. The universal properties of quotient and localization give the
   displayed k-algebra isomorphism. In one direction send X_i to phi(X_i), and
   z,w to the inverses of phi(b), phi(Delta) in S_g. In the other direction, I maps
   to zero since b annihilates I/J and b is invertible; descend P -> quotient to S,
   then extend to S_g since g is invertible. The composites fix X_i, z and w,
   and fix S and the inverse of g, respectively. Order the selected variables increasingly;
   permuting rows or columns changes the determinant only by a unit sign.
If there are no kernel generators, Delta is the empty determinant 1. If I/J=0,
take b=1. Thus zero equations and zero-dimensional regular points are included.
No global complete intersection, regular sequence, or smoothness theorem is needed. -/
theorem exists_jacobian_unit_presentation_of_regularAtMaximal
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsAlgClosed k] [Algebra.FiniteType k S]
    (m : Ideal S) (hm : m.IsMaximal)
    (hreg : IsRegularLocalRing (Localization.AtPrime m)) :
    ∃ (g : S), g ∉ m ∧
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
        (e : (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k]
          Localization.Away g) (i : Fin c → Fin n),
        StrictMono i ∧ IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range f))
          (Matrix.det (fun j l : Fin c ↦ MvPolynomial.pderiv (i l) (f j)))) := by sorry

end Algebra
