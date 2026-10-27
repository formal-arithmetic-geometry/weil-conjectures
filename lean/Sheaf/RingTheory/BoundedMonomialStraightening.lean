module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Defs

/-! # Degree control for bounded ordered monomials

Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed pp.200--204,
and Theorem 10.40, printed p.207. This is the abstract degree-tracking argument
with the bounded basis assumed, not a PBW independence theorem.
(blueprint: lem-sfb-bounded-monomial-straightening).

## Main definitions and statements

* `orderedGeneratorMonomial`: the ordered product denoted by y^a in the node.
* `boundedMonomialDegreeSpan`: the subspace denoted by P_d in the node.
* `bounded_monomial_straightening`: word degree bounds, multiplicativity, and
  the two leading-product formulas, including the empty-family case.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Algebra

/-- The ordered product y_1^a_1 ... y_n^a_n, with empty product 1.

Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed p.200;
the notation used in (blueprint: lem-sfb-bounded-monomial-straightening).
`List.ofFn` fixes increasing index order and requires no commutativity.
-/
def orderedGeneratorMonomial {A : Type v} [Monoid A] {n : ℕ}
    (y : Fin n → A) (a : Fin n → ℕ) : A :=
  (List.ofFn fun i : Fin n ↦ y i ^ a i).prod

/-- The span P_d of bounded ordered monomials of total degree at most d.

Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed pp.200--202,
and Theorem 10.40, printed p.207; the degree-tracking notation in
(blueprint: lem-sfb-bounded-monomial-straightening).
The integer bound retains negative degrees: their generating sets are empty.
-/
def boundedMonomialDegreeSpan (F : Type u) [Field F]
    {A : Type v} [Ring A] [Algebra F A] {n : ℕ}
    (y : Fin n → A) (q : ℕ) (d : ℤ) : Submodule F A :=
  Submodule.span F {z | ∃ a : Fin n → Fin q,
    (∑ i : Fin n, (a i : ℕ) : ℕ) ≤ d ∧
      z = orderedGeneratorMonomial y (fun i ↦ (a i : ℕ))}

/-- Lower-degree relations control products in a bounded ordered monomial basis.

Source: Milne, Algebraic Groups (2017), Theorem 10.36 and its degree/inversion
reordering proof, printed pp.200--204; Theorem 10.40, printed p.207.
(blueprint: lem-sfb-bounded-monomial-straightening).

Proof:
1. By def-weil-submodule-span, spans consist of finite linear combinations,
are closed under subtraction and scalar multiplication, and are monotone in
their generators. Thus P_d is increasing, P_{-1} = 0, and the empty word is in P_0.
2. Induct strongly on word length m. At fixed length also induct on the number
of inversions. An adjacent inverted pair j,i can be swapped; this decreases
inversions by one and preserves all label multiplicities.
3. The swap error is ev(u)(y_j y_i - y_i y_j)ev(v). Expanding its middle factor
in the span of 1 and the generators gives words of lengths m-2 or m-1. The outer
induction puts the error in P_{m-1}. The inner induction therefore shows that
each word differs from its sorted word by an element of P_{m-1}.
4. The sorted word has a multiplicity vector c of total degree m. If c is bounded,
it is a generator of P_m. Otherwise factor q consecutive copies of some y_i.
Expanding y_i^q in the span of 1 and the generators leaves words of lengths
m-q or m-q+1, both at most m-1 since q >= 2. Outer induction puts their values
in P_{m-1}. Adding the sorting error proves the word bound, and proves the
stronger bound P_{m-1} whenever some multiplicity is at least q.
5. Apply this calculation to the concatenation of the ordered words for a and b.
If a+b is bounded its sorted value is y^(a+b), giving the first leading formula.
Otherwise Step 4 gives the second formula. For a=b=0 the first difference is 0
in P_{-1}; the second case cannot occur.
6. Expand elements of P_r and P_s into bounded monomials. Bilinearity expresses
their product as a linear combination of words of length at most r+s. The word
bound and monotonicity put each term in P_{r+s}. Taking the span of products
gives the asserted submodule inclusion, also when r or s is zero.
7. If n=0 there is one bounded exponent vector and its monomial is 1. The basis
hypothesis gives A = F·1; no positive-length word exists, and unitality gives
1·1=1. The field throughout is def-weil-field, namely Mathlib's `Field`.
-/
theorem bounded_monomial_straightening
    (F : Type u) [Field F] (A : Type v) [Ring A] [Algebra F A]
    (n q : ℕ) (hq : 2 ≤ q) (y : Fin n → A)
    (hbasis : ∃ b : Module.Basis (Fin n → Fin q) F A,
      ∀ a : Fin n → Fin q, b a = orderedGeneratorMonomial y (fun i ↦ (a i : ℕ)))
    (hcomm : ∀ i j : Fin n,
      y j * y i - y i * y j ∈ Submodule.span F (insert (1 : A) (Set.range y)))
    (hpower : ∀ i : Fin n,
      y i ^ q ∈ Submodule.span F (insert (1 : A) (Set.range y))) :
    (∀ d : ℤ, d < 0 → boundedMonomialDegreeSpan F y q d = ⊥) ∧
    (∀ w : List (Fin n), (w.map y).prod ∈
      boundedMonomialDegreeSpan F y q (w.length : ℤ)) ∧
    (∀ r s : ℤ, 0 ≤ r → 0 ≤ s →
      Submodule.span F {z | ∃ x ∈ boundedMonomialDegreeSpan F y q r,
        ∃ t ∈ boundedMonomialDegreeSpan F y q s, z = x * t} ≤
          boundedMonomialDegreeSpan F y q (r + s)) ∧
    (∀ a b : Fin n → Fin q,
      ((∀ i : Fin n, (a i : ℕ) + (b i : ℕ) < q) →
        orderedGeneratorMonomial y (fun i ↦ (a i : ℕ)) *
            orderedGeneratorMonomial y (fun i ↦ (b i : ℕ)) -
          orderedGeneratorMonomial y (fun i ↦ (a i : ℕ) + (b i : ℕ)) ∈
            boundedMonomialDegreeSpan F y q
              (((∑ i : Fin n, (a i : ℕ)) : ℤ) + (∑ i : Fin n, (b i : ℕ)) - 1)) ∧
      ((∃ i : Fin n, q ≤ (a i : ℕ) + (b i : ℕ)) →
        orderedGeneratorMonomial y (fun i ↦ (a i : ℕ)) *
          orderedGeneratorMonomial y (fun i ↦ (b i : ℕ)) ∈
            boundedMonomialDegreeSpan F y q
              (((∑ i : Fin n, (a i : ℕ)) : ℤ) + (∑ i : Fin n, (b i : ℕ)) - 1))) ∧
    (n = 0 → (⊤ : Submodule F A) = Submodule.span F {(1 : A)} ∧
      (1 : A) * 1 = 1) := by
  sorry

end Algebra
