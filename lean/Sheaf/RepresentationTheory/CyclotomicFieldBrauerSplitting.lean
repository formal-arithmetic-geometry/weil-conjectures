module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Sheaf.RepresentationTheory.SemisimpleScalarExtensionCriterion

/-! # Brauer splitting over fields containing exponent roots

Source: ILO, Exposé X, Proposition 1.2, printed p.138, representation lifting before (5),
citing Serre 1978, Chapter 12 §2.3 and Chapter 13 §14.4. This is the auxiliary
characteristic-zero Brauer splitting theorem used there; Serre is not yet obtained.
(blueprint: lem-per-cyclotomic-field-brauer-splitting)
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- A characteristic-zero field containing a primitive root of an exponent of a finite
group splits its group algebra into a nonempty finite product of full matrix algebras.
The group algebra is Mathlib's finite formal linear combinations, with convolution
multiplication, so its basis elements satisfy `[g][h] = [gh]`.

Source: ILO, Exposé X, Proposition 1.2, printed p.138, representation lifting before (5),
citing Serre 1978, Chapter 12 §2.3 and Chapter 13 §14.4; auxiliary Brauer splitting input.

Proof:
1. By lem-per-maschke-finite-group-algebra, characteristic zero makes K[G] semisimple.
   Apply lem-per-semisimple-algebra-matrix-division to get a finite product of positive
   matrix algebras over finite-dimensional division K-algebras D_i. The product is nonempty
   because the basis vector [1] is nonzero. Choose an algebraic closure Ω using
   lem-pc-algebraic-closure-exists-unique.
2. The powers 1, ζ, ..., ζ^(N-1) are distinct by the primitive-root hypothesis and exhaust
   the N roots of X^N-1 in Ω. Thus all Nth roots of unity in Ω belong to K.
3. Apply lem-per-brauer-monomial-induction over Ω. Each linear character of a subgroup H
   has Nth-root values, hence values in K. Its induced representation has the K-basis
   indexed by G/H, with action a e_t = λ(h) e_t' when a t = t' h. This is the same coset
   basis as the quotient defining induction, and scalar extension preserves its matrices.
   Brauer induction therefore makes every representation class an integer combination
   of scalar extensions of K-representations.
4. Identify group representations with group-algebra modules and Ω ⊗[K] K[G] with Ω[G]
   by x ⊗ sum a_g[g] mapping to sum (x a_g)[g]; the inverse sends sum b_g[g] to
   sum b_g ⊗ [g]. The tensor relations of def-weil-pbc-module-tensor-product verify this.
   Hence scalar extension is surjective on the split Grothendieck groups used in
   lem-per-semisimple-scalar-extension-kzero-criterion.
5. Maschke also makes Ω[G] semisimple. The scalar-extension criterion makes every
   structural map K → D_i bijective. Apply its inverse entrywise to the matrix factors
   of step 1, obtaining the asserted K-algebra isomorphism with the same positive sizes.

(blueprint: lem-per-cyclotomic-field-brauer-splitting) -/
theorem exists_algEquiv_pi_matrix_of_exponent_roots
    (K : Type u) [Field K] [CharZero K] (N : ℕ) (hN : 0 < N)
    (ζ : K) (hζ : ζ ^ N = 1) (hζprim : ∀ j : ℕ, 0 < j → j < N → ζ ^ j ≠ 1)
    (G : Type v) [Group G] [Finite G] (hG : ∀ g : G, g ^ N = 1) :
    ∃ r : ℕ, 0 < r ∧ ∃ d : Fin r → ℕ, (∀ i : Fin r, 0 < d i) ∧
      Nonempty (MonoidAlgebra K G ≃ₐ[K] ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K) := by
  sorry

end MonoidAlgebra
