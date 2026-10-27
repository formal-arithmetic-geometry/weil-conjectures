/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot

/-!
# Diagonal root invariants and the nonnegative exponent lattice

Source: ILO, Travaux de Gabber, Exposé IX, Proposition 2.1 proof, printed p.133;
Exposé VI 2.2--2.3, printed pp.72--73.
(blueprint: lem-per-diagonal-root-invariant-monoid-algebra).

The intermediate objects are existentially bound with their exact defining equations.
In particular, neither the lattice, the diagonal action, the fixed subalgebra nor either
base algebra structure is an arbitrary choice. This states their construction and all
properties together without selecting data from the postponed theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace RingTheory

/-- The diagonal fixed algebra is the base change of the nonnegative character lattice.
Source: ILO IX, Proposition 2.1 proof, p.133, and VI 2.2--2.3, pp.72--73
(blueprint: lem-per-diagonal-root-invariant-monoid-algebra).

Proof plan (the eight steps of the DAG node):
1. The character congruences define a subgroup L containing the integer lattice J.
Reduction of numerators modulo n embeds L/J in (Z/n)^r, proving finiteness and exponent n.
2. Divide every nonnegative numerator coordinate by n. The resulting finite residue box
and the standard integral generators generate Q. Its embedding in L gives integrality;
translation by a sufficiently positive integral vector expresses every lattice element
as a difference of elements of Q. Nonnegativity proves saturation and sharpness.
3. Successively adjoin the roots. Polynomial evaluation and quotient universal properties
(def-weil-pbc-mv-polynomial-ring, def-weil-pbc-algebra-hom-quotient), followed by the monic
power basis (lem-weil-pbc-monic-quotient-free), give the basis indexed by exponents below n.
The zero coefficient ring is treated separately, without a nontriviality assumption.
4. Scaling the generators preserves the relations and defines the diagonal action.
In its monomial basis, an invariant coefficient with nontrivial character is killed by
a unit 1-zeta^a, hence vanishes. The invariant monomials therefore form a basis.
5. Unique residue-box decomposition makes Z[Q] free over Z[P] on those same monomials.
6. Base change of this basis (lem-weil-pbc-free-module-base-change-free) and the algebra
tensor pushout (lem-weil-pbc-algebra-tensor-pushout-universal-property) give the map with
the stated pure-tensor formula, balanced because x_i^n=t_i.
7. The map identifies the two bases, so is an A-algebra isomorphism. Balancing gives the
parameter formula, and taking nth powers gives the identity for every q.
8. Empty tuples, n=1, zero parameters and zero divisors require no change: only the
specified character differences are cancelled. Thus all boundary cases are included. -/
theorem diagonal_root_invariant_monoid_algebra
    (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (hnA : IsUnit (n : A))
    (ζ : Aˣ) (hζ : ζ ^ n = 1)
    (hsep : ∀ a : ℕ, 1 ≤ a → a < n → IsUnit (1 - (ζ : A) ^ a))
    (r : ℕ) (t : Fin r → A) (H : AddSubgroup (Fin r → ZMod n)) :
    ∃ (I : Ideal (MvPolynomial (Fin r) A))
      (x : Fin r → MvPolynomial (Fin r) A ⧸ I)
      (L : AddSubgroup (Fin r → ℚ)) (Q : AddSubmonoid L)
      (ι : (Fin r → ℕ) →+ Q) (J : AddSubgroup L),
      I = Ideal.span (Set.range (fun i : Fin r ↦
        (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i))) ∧
      (∀ i, x i = Ideal.Quotient.mk I (MvPolynomial.X i)) ∧
      (∀ l : Fin r → ℚ, l ∈ L ↔ ∃ a : Fin r → ℤ,
        (∀ i, l i = (a i : ℚ) / (n : ℚ)) ∧
        ∀ h : H, ∑ i, (h.1 i) * (a i : ZMod n) = 0) ∧
      (∀ l : L, l ∈ Q ↔ ∀ i, 0 ≤ l.1 i) ∧
      (∀ (p : Fin r → ℕ) (i : Fin r), (ι p).1.1 i = (p i : ℚ)) ∧
      (∀ l : L, l ∈ J ↔ ∃ a : Fin r → ℤ, ∀ i, l.1 i = (a i : ℚ)) ∧
      AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative Q) ∧
      (∀ q : Q, IsAddUnit q ↔ q = 0) ∧
      (∃ e : Algebra.GrothendieckAddGroup Q ≃+ L,
        ∀ q : Q, e (Algebra.GrothendieckAddGroup.of q) = q.1) ∧
      Function.Injective ι ∧
      (∀ q : Q, ∃ p : Fin r → ℕ, n • q = ι p) ∧
      Finite (L ⧸ J) ∧ (∀ c : L ⧸ J, n • c = 0) ∧
      ∃ (α : Algebra (AddMonoidAlgebra ℤ (Fin r → ℕ)) A)
        (β : Algebra (AddMonoidAlgebra ℤ (Fin r → ℕ)) (AddMonoidAlgebra ℤ Q)),
        (∀ p : Fin r → ℕ,
          algebraMap (AddMonoidAlgebra ℤ (Fin r → ℕ)) A
            (AddMonoidAlgebra.single p 1) = ∏ i, t i ^ p i) ∧
        (∀ p : Fin r → ℕ,
          algebraMap (AddMonoidAlgebra ℤ (Fin r → ℕ)) (AddMonoidAlgebra ℤ Q)
            (AddMonoidAlgebra.single p 1) = AddMonoidAlgebra.single (ι p) 1) ∧
        ∃ σ : Multiplicative H →*
            ((MvPolynomial (Fin r) A ⧸ I) ≃ₐ[A] (MvPolynomial (Fin r) A ⧸ I)),
          (∀ (h : H) (i : Fin r), σ (Multiplicative.ofAdd h) (x i) =
            algebraMap A (MvPolynomial (Fin r) A ⧸ I) ((ζ : A) ^ (h.1 i).val) * x i) ∧
          ∃ C : Subalgebra A (MvPolynomial (Fin r) A ⧸ I),
            (∀ b, b ∈ C ↔ ∀ h : H, σ (Multiplicative.ofAdd h) b = b) ∧
            ∃ Φ : (A ⊗[AddMonoidAlgebra ℤ (Fin r → ℕ)] AddMonoidAlgebra ℤ Q) ≃ₐ[A] C,
              (∀ (a : A) (q : Q),
                (Φ (a ⊗ₜ AddMonoidAlgebra.single q 1)).1 =
                  algebraMap A (MvPolynomial (Fin r) A ⧸ I) a *
                    ∏ i, x i ^ (((n : ℚ) * q.1.1 i).num.toNat)) ∧
              (∀ i : Fin r,
                Φ (1 ⊗ₜ AddMonoidAlgebra.single (ι (Pi.single i 1)) 1) =
                  algebraMap A C (t i)) ∧
              (∀ q : Q, (Φ (1 ⊗ₜ AddMonoidAlgebra.single q 1)) ^ n =
                algebraMap A C (∏ i, t i ^ (((n : ℚ) * q.1.1 i).num.toNat))) := by
  sorry

end RingTheory
