module

public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalEndomorphismAction
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Sheaf.RingTheory.MultiplicativePolynomialNorm
import Sheaf.NumberTheory.Padics.RootProductRigidity
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Localization.BaseChange

/-! # Rational characteristic polynomials of abelian endomorphisms

Source: Milne, Abelian Varieties, I Theorem 10.9, Remark 10.11 and Proposition 10.20,
pp. 46--52 (blueprint: lem-sfb-abelian-tate-charpoly).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry.IsAbelianVariety

/-- The characteristic polynomial of the canonical rational Tate action. The finite-dimensional
instance is supplied by the recorded Tate rank theorem, so it is not an additional hypothesis.
Source: Milne, I Proposition 10.20, p. 50
(blueprint: lem-sfb-abelian-tate-charpoly). -/
noncomputable def rationalEndomorphismTateCharpoly {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k) (f : RationalEndomorphisms A) :
    Polynomial ℚ_[ℓ] :=
  let e := (nonempty_linearEquiv_rationalTateModule ℓ A (ringChar k) hℓ).some
  letI := FiniteDimensional.of_injective e.toLinearMap e.injective
  (rationalEndomorphismTateAction A ℓ f).charpoly

/-- Every rational group-scheme endomorphism has a unique monic rational characteristic
polynomial, simultaneously realizing every prime-to-characteristic Tate action. Integral
endomorphisms have integral coefficients, and the dimension-zero polynomial is one.
Source: Milne, I Theorem 10.9, Remark 10.11, Proposition 10.20, pp. 46--52
(blueprint: lem-sfb-abelian-tate-charpoly).

Proof:
1. By prop-av-tate-rank, the rational Tate module has dimension twice dim A. In dimension
zero its determinant polynomial is the empty determinant, one.
2. For positive dimension, lem-sfb-abelian-hom-finite-free makes the integral endomorphism
ring finite free. By lem-sfb-abelian-degree-polynomial and
lem-sfb-abelian-degree-multiplicative, its rational degree function is a multiplicative
homogeneous polynomial norm of degree twice dim A. Multiplicativity extends to fractions
using lem-sfb-rational-tensor-fractions.
3. Apply lem-sfb-multiplicative-polynomial-norm to delta(t - a). For an integral a,
Cayley--Hamilton on left multiplication on the finite free integral endomorphism ring gives
a monic integral annihilator of a (lem-weil-cayley-hamilton-free-module). The norm lemma's
integrality clause therefore gives integral coefficients; integer values alone do not suffice.
4. For an allowable prime, triangularize the Tate action over an algebraic closure using
p-linear-triangular. Polynomial evaluation has diagonal entries F(b_i).
The norm lemma's root-product identity and lem-sfb-abelian-degree-tate-valuation identify
the adic absolute values of the root products for every integral F, including non-isogenies.
The two polynomials are monic of degree twice dim A (lem-weil-charpoly-monic-degree).
Apply lem-sfb-padic-resultant-rigidity to identify them.
5. For a rational endomorphism f, clear denominators: n f = a with positive n and integral a.
Set P_f(X) = n^(-2 dim A) P_a(n X). Factoring n from every row of the Tate determinant
proves compatibility at every allowable prime. When f is integral take n = 1.
6. Take the prime 2 unless the characteristic is 2, in which case take 3. The rational
embedding into this adic field is injective, so equality of realizations implies equality
of rational polynomials coefficientwise. This also proves independence of denominators. -/
theorem existsUnique_rational_tate_charpoly {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (f : RationalEndomorphisms A) :
    ∃ P : Polynomial ℚ,
      P.Monic ∧ P.natDegree = 2 * dim A ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k),
        P.map (algebraMap ℚ ℚ_[ℓ]) = rationalEndomorphismTateCharpoly A ℓ hℓ f) ∧
      (∀ Q : Polynomial ℚ, Q.Monic → Q.natDegree = 2 * dim A →
        (∀ (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k),
          Q.map (algebraMap ℚ ℚ_[ℓ]) = rationalEndomorphismTateCharpoly A ℓ hℓ f) → Q = P) ∧
      ((∃ a : Additive (Grp.mk A ⟶ Grp.mk A), f = a ⊗ₜ[ℤ] (1 : ℚ)) →
        ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ)) ∧
      (dim A = 0 → P = 1) := by
  sorry

end AlgebraicGeometry.IsAbelianVariety
