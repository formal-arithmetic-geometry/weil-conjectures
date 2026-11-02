/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilPointFlags.CondensedPointWeilFlagsStatement

/-! # Constructible native condensed Weil flags from matrix data

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph beginning
“All these finitely many subschemes”, dimension-zero Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-filtration-data).

The point model, free modules and scalar-normalized Frobenius matrix are the
parent's canonical definitions. The Weil category and purity are NativeL2's.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- A full constructible Weil flag for any embedding of the coefficient field into C.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph beginning
“All these finitely many subschemes”, dimension-zero Jordan filtrations
(blueprint: lem-zl-condensed-point-weil-flags-filtration-data).

Proof, following the five steps of the node:
1. Induct on the dimension of an arbitrary finite-dimensional Omega-space with an
invertible operator. In positive dimension choose a nonzero eigenvector v, using
algebraic closure. Its eigenvalue alpha is nonzero by injectivity. The line Omega v
is stable under A and its inverse, since A^{-1}v = alpha^{-1}v. Both descend to
mutually inverse operators on the quotient. Pull back the inductively constructed
quotient flag and precede it by zero. Inverse images are stable under both operators,
their dimensions increase by one, and the final term is the whole space. In dimension
zero use the zero flag. Apply this to the specified operator on Omega^d.
2. Extend a basis one vector at a time along the invariant flag. If P is its
change-of-basis matrix, C = P^{-1} A P is upper triangular. Each top-left block C_j
is invertible because the corresponding span is stable under the inverse. On the
one-dimensional successive quotient its diagonal scalar alpha_j is therefore nonzero.
Coordinate inclusion I_j and last-coordinate projection pi_j satisfy
C_j I_j = I_j C_{j-1} and pi_j C_j = alpha_j pi_j by block multiplication.
3. Exact fully faithful scalar realization at the geometric point identifies maps
of finite free B-modules with Omega-matrices. The canonical point-module comparison
for Frobenius is natural for these matrices. Give B^j the Weil structure C_j and
inverse C_j^{-1}. The two block equations make inclusion and projection equivariant.
The map e^{-1}P is a Weil isomorphism from the last term to M, since AP = PC;
its inverse is P^{-1}e. This construction uses no diagonalization.
4. The coordinate sequence from B^{j-1} to B^j to B is split exact on module sheaves.
Inclusion has a coordinate retraction, so it is monic also among Weil maps. An
equivariant map killing the inclusion factors uniquely through pi_j as a module map.
Its factor is equivariant: the two equivariance composites agree after precomposition
with the Frobenius pullback of pi_j, which is split epic. Thus (B, alpha_j) is the
actual Weil cokernel. Every B^n is constructible: on the identity cover of the single
stratum it has the finitely presented scalar model Omega^n, including n = 0. The
coefficient heart has exact inclusion, so these are constructible heart quotients.
Compose the monic inclusions and the last isomorphism to obtain actual subobjects of M.
5. The base has one closed point, of residue cardinality q. Its local geometric
Frobenius is one application of the Weil structure, hence alpha_j on the quotient.
Put r = norm(iota(alpha_j)). A field embedding is injective, so r > 0. Since q > 1,
q^{(2 log_q r)/2} = exp(log(q) log(r) / log(q)) = r. This is punctual purity at the
only eigenvalue, with every compatible geometric lift giving the same scalar.
No inverse or surjectivity of iota is used. When d = 0 the chosen rank-zero basis
identifies M with zero and every quotient assertion is vacuous. -/
theorem flag_filtration_data_embedding (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : NativeL2.WeilModule D l (pointModel D)) (d : ℕ)
    (e : M.carrier ≅ free D l d)
    (A : (Fin d → PadicAlgCl l) ≃ₗ[PadicAlgCl l] (Fin d → PadicAlgCl l))
    (_hA : A.toLinearMap = (frobeniusMatrix D l M e).mulVecLin) :
    ∃ (G : Fin (d + 1) → NativeL2.WeilModule D l (pointModel D))
      (f : ∀ j : Fin d, G j.castSucc ⟶ G j.succ),
      IsZero (G 0) ∧ Nonempty (G (Fin.last d) ≅ M) ∧
      (∀ j, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (pointSpace D) (G j).carrier) ∧
      (∀ j, Nonempty ((G j).carrier ≅ free D l j.val)) ∧
      (∀ j : Fin d, Mono (f j)) ∧
      ∀ j : Fin d,
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (pointSpace D) (cokernel (f j)).carrier ∧
        ∃ (alpha : (PadicAlgCl l)ˣ)
          (b : (cokernel (f j)).carrier ≅ free D l 1),
          frobeniusMatrix D l (cokernel (f j)) b =
            (fun _ _ ↦ (alpha : PadicAlgCl l)) ∧
          NativeL2.Pure D l (pointModel D) (cokernel (f j)) iota
            (2 * Real.logb (D.q : ℝ) ‖iota (alpha : PadicAlgCl l)‖) := by
  sorry

end WeilConjectures.CondensedWeilPointFlags
