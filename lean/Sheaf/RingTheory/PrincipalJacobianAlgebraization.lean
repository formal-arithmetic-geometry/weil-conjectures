/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.ConormalTorsionAlgebraization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Principal-ideal algebraization of a torsion conormal presentation

Source: Stacks Project, restricted.tex, Tag 0ALS (lemma-approximate-principal),
using Tag 0AJU, condition (3)
(blueprint: lem-per-principal-jacobian-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- A complete quotient of a completed polynomial ring with power-torsion kernel and
cokernel of its continuous conormal differential has a finite type algebraization.

Source: Stacks Project, restricted.tex, Tag 0ALS, via Tag 0AJU(3) and Tag 0GAW
(blueprint: lem-per-principal-jacobian-algebraization).

Proof:
1. Finite type polynomial rings, their completions and their quotients are Noetherian,
   by lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-adic-completion-noetherian and lem-weil-pbc-surjective-image-noetherian.
2. Write M = J/J² and delta for its differential. Choose alpha with delta alpha = a^c.
   Kernel annihilation gives a^c alpha delta = a^(2c). Thus beta = a^c alpha is a
   homotopy for a^(2c). Lift beta's basis values to f_i in J. Their Jacobian determinant
   is Delta = a^(2cr) in E. Put d = 2c(r+1) and b = a^(2c); then b Delta = a^d,
   and a^d J is contained in (f_i) + J².
3. The a-power torsion ideal U of E is finitely generated; choose t with a^t U = 0.
   Then U intersect a^t E = 0. Put h = 2d and choose n > max(2h,h+t).
   By lem-weil-pbc-adic-completion-mod-power choose polynomial approximations f'_i
   modulo a^n. Let Delta' be their Jacobian determinant and construct the actual
   finite type algebra C = A[x_1,...,x_r,z]/(f'_i,z Delta'-a^d).
4. By lem-weil-pbc-completion-exact-finite-modules and
   lem-weil-pbc-completion-finite-module-tensor, D = C completed along (a) is the
   quotient of the completed polynomial ring by these same equations. It is Noetherian
   and complete by lem-weil-pbc-adic-completion-noetherian and
   lem-weil-pbc-adic-completion-mod-ideal.
5. The square Jacobian matrix T for these equations has determinant (Delta')².
   By lem-weil-pbc-matrix-adjugate-identity, the equation-generator map composed with
   adj(T), then multiplied by z², gives H with delta_D H = H delta_D = a^(2d).
6. Send x_i to the original classes and z to b modulo a^n. Polynomial approximation
   makes this an A-algebra map D to E/a^n E. Apply
   lem-per-principal-adic-homomorphism-lift with h = 2d and the torsion bound t to
   obtain phi : D to E agreeing with this map modulo a^(n-h), hence modulo a.
7. Original variable classes generate E/aE, so phi is surjective modulo a. Apply
   lem-weil-pbc-complete-source-surjective-mod-ideal to the complete source D and
   Hausdorff target E to conclude surjectivity. Set K = ker phi.
8. Apply lem-per-completed-cotangent-transitivity to D to E, using the zero-variable
   relative presentation. Its exact fragment is ker delta to K/K² to
   E tensor_D coker delta_D. The outer terms are killed by a^c and a^h respectively;
   exactness therefore shows a^(h+c) kills K/K².
9. Apply lem-per-conormal-torsion-algebraization to the surjection from the completion
   of the finite type algebra C to E and this conormal torsion. It gives the desired
   finite type algebra and A-algebra equivalence of its completion with E. -/
theorem principalJacobianAlgebraization {A : Type u} [CommRing A] [IsNoetherianRing A]
    (a : A) (r : ℕ) (J : Ideal (rigPolynomialCompletion (Ideal.span {a}) r))
    [IsAdicComplete (Ideal.span {a}) (rigPolynomialCompletion (Ideal.span {a}) r ⧸ J)]
    (c : ℕ)
    (hkernel : (Ideal.span {a}) ^ c •
      (rigJacobianDifferential r (Ideal.span {a}) J).ker ≤ ⊥)
    (hcoker : (Ideal.span {a}) ^ c •
      (⊤ : Submodule A ((Fin r → (rigPolynomialCompletion (Ideal.span {a}) r ⧸ J)) ⧸
        (rigJacobianDifferential r (Ideal.span {a}) J).range)) ≤ ⊥) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      RingHom.FiniteType (algebraMap A C) ∧
        Nonempty (AdicCompletion ((Ideal.span {a}).map (algebraMap A C)) C ≃ₐ[A]
          (rigPolynomialCompletion (Ideal.span {a}) r ⧸ J)) := by
  sorry

end AlgebraicGeometry
