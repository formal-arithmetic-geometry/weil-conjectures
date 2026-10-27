module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Data.Nat.Choose.Sum

/-!
# A truncated monomial basis for the semilinear restricted symmetric algebra

Source: Milne, Algebraic Groups, Definition 10.39 and Theorem 10.40, printed pp.206–207,
and Lemma 14.43, printed p.294 (blueprint: lem-sfb-semilinear-restricted-symmetric-basis).
The zero-bracket specialization allows arbitrary vector spaces over any field of prime
characteristic; neither perfectness nor finite generation under the semilinear map is needed.
-/

@[expose] public section

universe u v w

namespace SymmetricAlgebra

/-- The monomials with all exponents below `p` form a basis of the quotient of the
symmetric algebra by `ι(x)^p - ι(T x)`, and the induced linear map from `V` is injective.
The quotient and its canonical map are written directly using Mathlib's constructions.

Source: Milne, Algebraic Groups, Theorem 10.40, printed p.207, specialized to a zero-bracket
restricted Lie algebra; Lemma 14.43, printed p.294
(blueprint: lem-sfb-semilinear-restricted-symmetric-basis).

Proof plan:
1. The ordinary monomial basis is `b.symmetricAlgebra`
   [lem-sfb-symmetric-algebra-monomial-basis]. Filter by total degree. Multiplication adds
   degrees, and `ι(T (b i))` has degree at most one by the finite basis expansion of `T (b i)`.
2. Write `E_i = ι(b i)` and `c_i = E_i^p - ι(T (b i))`. The commuting binomial expansion
   [lem-sfb-commuting-binomial-expansion] and the vanishing of intermediate binomial
   coefficients in the field [def-weil-field] give Frobenius additivity. For a finite
   expansion `x = ∑ a_i b i`, semilinearity yields
   `ι(x)^p - ι(T x) = ∑ a_i^p c_i`. Thus all relations generate exactly the ideal `(c_i)`.
3. For finitely supported exponents `a_i < p` and `d_i ≥ 0`, the mixed monomial
   `E^a ∏ c_i^{d_i}` equals `E^{a + p*d}` plus terms of strictly smaller total degree.
   Every nonleading term replaces a degree-`p` factor by one of degree at most one.
   Coordinatewise Euclidean division uniquely parametrizes every exponent by `(a,d)`.
4. These mixed monomials span by induction on total degree. They are independent by
   comparing the highest-degree terms in any finite relation with the ordinary monomial
   basis [lem-sfb-symmetric-algebra-monomial-basis]. Only a finite maximum is needed.
5. Multiplication by `c_i` increments `d_i`; hence the relation ideal is exactly the span
   of mixed monomials with `d ≠ 0`. The quotient map has that ideal as its kernel
   [def-weil-pbc-algebra-hom-quotient]. The remaining monomials, with `d = 0`, therefore
   give exactly the displayed basis. `Finsupp.prod` makes the zero exponent's product `1`.
6. Since `p ≥ 2`, the unit exponents belong to this basis. Independence then proves
   injectivity of the induced linear map by a finite basis expansion in `V`. For the
   empty index set the sole monomial is `1` and `V = 0`. No finite-dimensional invariant
   subspace, finite generation under `T`, or extraction of scalar `p`th roots is used. -/
theorem exists_basis_semilinear_restricted_quotient
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (T : V →+ V) (hT : ∀ (c : k) (x : V), T (c • x) = c ^ p • T x)
    {I : Type w} (b : Module.Basis I k V) :
    (∃ c : Module.Basis {a : I →₀ ℕ // ∀ i : I, a i < p} k
        ((SymmetricAlgebra k V) ⧸ Ideal.span
          (Set.range fun x : V => (ι k V x) ^ p - ι k V (T x))),
      ∀ a : {a : I →₀ ℕ // ∀ i : I, a i < p},
        c a = a.val.prod (fun i n =>
          (Ideal.Quotient.mkₐ k (Ideal.span
            (Set.range fun x : V => (ι k V x) ^ p - ι k V (T x)))
              (ι k V (b i))) ^ n)) ∧
    Function.Injective
      ((Ideal.Quotient.mkₐ k (Ideal.span
          (Set.range fun x : V => (ι k V x) ^ p - ι k V (T x)))).toLinearMap.comp
        (ι k V)) := by
  sorry

end SymmetricAlgebra
