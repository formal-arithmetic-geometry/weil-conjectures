## Worker report

The module `Sheaf.RingTheory.HomogeneousAdditivePolynomial` states
`MvPolynomial.homogeneous_additive_monomial_classification`, with its sole proof
`sorry`. No definitions, auxiliary theorems, new nodes, dependency repairs, or
statement corrections are needed. Only the item's `lean` field is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k is `{k : Type u} [Field k]`, with explicitly declared universe u.
- The arbitrary integer n >= 0 is `n : ℕ`; `Fin n` labels exactly n variables,
  differing from 1,...,n only by the indexing bijection. No positivity or
  nonemptiness assumption on n is imposed.
- P=k[Z_1,...,Z_n] is `MvPolynomial (Fin n) k`.
- The positive degree is `d : ℕ` with `hd : 0 < d`.
- The nonzero element of P_d is `f : MvPolynomial (Fin n) k`, `hf : f ≠ 0`,
  and `hhom : f.IsHomogeneous d`. Mathlib defines `IsHomogeneous` as weighted
  homogeneity with every variable of weight one, exactly the total-degree
  grading; `mem_homogeneousSubmodule` identifies this with membership in P_d.
  The general `GradedAlgebra.IsStandard` dependency is imported; its data are
  not extra hypotheses because the polynomial ring's grading is fixed already.
- The ring on two disjoint tuples is `MvPolynomial (Fin n ⊕ Fin n) k`.
  `X (Sum.inl j)` and `X (Sum.inr j)` are independent Z_j and W_j.
  The left side of each equivalence is explicitly the equality of `aeval`
  at Z+W with the sum of `aeval` at Z and at W, in that polynomial ring.
  Thus this is a formal polynomial identity, including over finite fields.
  This formula is written inline using the recorded evaluation declaration;
  it introduces no missing independent notion or private replacement.
- The characteristic is Mathlib's `ringChar k`. The first conjunct begins
  `ringChar k = 0 →` and asserts the stated equivalence with
  `d = 1 ∧ ∃ a : Fin n → k, f = ∑ j : Fin n, C (a j) * X j`.
  Multiplication by `C (a j)` is multiplication by the coefficient in P.
- The second conjunct quantifies `∀ p : ℕ, 0 < p → ringChar k = p →`.
  Its equivalence concludes `∃ e : ℕ, d = p ^ e ∧ ∃ a : Fin n → k, ...`,
  with the sum `∑ j : Fin n, C (a j) * X j ^ (p ^ e)`.
  Natural e is exactly the nonnegative integer exponent called a in the node.
  There is no additional primality hypothesis: primality follows from the
  positive characteristic of the field, as in the node's proof.
- Both occurrences of “if and only if” are Lean `↔`; the two conditional
  characteristic assertions are joined by `∧`, preserving both cases.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs. Its extension of
  CommRing and DivisionRing gives precisely the field in the statement.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.C`/`X`,
  Mathlib.Algebra.MvPolynomial.Basic; `MvPolynomial.aeval`,
  Mathlib.Algebra.MvPolynomial.Eval. The full signatures and evaluation
  docstring were read, as was `MvPolynomial.algHom_ext` for uniqueness.
- `def-pc-standard-graded-algebra`: `GradedAlgebra.IsStandard`,
  WeilConjectures.RingTheory.GradedAlgebra.Standard, read with its docstring
  and graded-algebra context. For the specified polynomial grading the exact
  specialized Mathlib predicate is `MvPolynomial.IsHomogeneous`, with
  `MvPolynomial.homogeneousSubmodule` and `mem_homogeneousSubmodule`, in
  Mathlib.RingTheory.MvPolynomial.Homogeneous. These are existing definitions,
  not a replacement grading and not additional standardness assumptions.
- `def-pc-field-characteristic`: `CharP`, `ringChar`, `ringChar.spec` and
  `ringChar.eq_iff`, Mathlib.Algebra.CharP.Defs; their defining signatures were
  read. `ringChar` gives the characteristic without adding a CharP instance
  as a hypothesis to either case.
- Proof-only dependency `lem-pur-commutative-ring-binomial-expansion`:
  `add_pow`, Mathlib.Data.Nat.Choose.Sum, full signature read.
- Proof-only dependency `lem-trf-binomial-vanishing-prime-power`:
  `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`,
  Mathlib.Data.Nat.Choose.Lucas, signature and docstring read. This is the
  dependency's mathlib_match and needs no separate Lean record or repair.
- Proof-only dependency `def-weil-ring-frobenius`:
  `iterateFrobeniusOfPrime` and `iterateFrobeniusOfPrime_apply`,
  WeilConjectures.Mathlib.Algebra.CharP.Lemmas, full definitions and docstrings
  read. All three proof-only modules are plain imports; statement dependencies
  are public imports. The theorem docstring records all four DAG proof steps.

Sources: Dietel's dissertation was opened at https://d-nb.info/1068056037/34
and Proposition 3.3.5 and Definition 1.4.1 were read. Proposition 3.3.5
classifies nonzero homogeneous primitive polynomials over a domain: degree
one or pure characteristic-power monomials. Its specialization to fields,
identifying the primitive identity with substitution in two disjoint tuples,
is exactly the unchanged node. Definition 1.4.1 gives the positive-characteristic
notation. The DAG distinguishes this supporting source from the motivational
ILO ancestor; no claim is made that ILO states this classification.

Edge cases checked mathematically before writing:

- n=0: a positive-degree homogeneous polynomial in no variables is zero, so
  the nonzero hypothesis is impossible. No n>0 restriction is introduced.
- d=0 and f=0 are explicitly excluded, as in the node. Without f≠0 the degree
  conclusion would be false, since zero is homogeneous in every degree.
- d=1: every linear form satisfies the identity in every characteristic;
  e=0 gives p^0=1 in the second equivalence.
- Characteristic 2, d=2: pure squares are additive; a mixed term Z_1 Z_2
  is not, since its cross terms involve distinct variables in the doubled ring.
- Characteristic 2, d=3: X^3 has nonzero cross terms and is not additive.
- Characteristic 3, d=6: the coefficient choose(6,3)=20 is nonzero modulo 3,
  so X^6 is not additive; 6 is not a power of 3.
- Characteristic zero, d>1: the coefficient d of X Y^(d-1) obstructs additivity.
- Finite fields and imperfect fields are allowed without extra assumptions.
  Over F_p the nonhomogeneous polynomial X^p-X vanishes as a function but
  is a nonzero formal polynomial, illustrating why pointwise testing does
  not replace the formal identity.
- Coefficients may vanish individually; the given f≠0 forces at least one
  nonzero coefficient when either displayed representation holds.

Searches made on 2026-10-24 through the prescribed msearch.py wrapper:

- `leanfinder`: “Homogeneous additive polynomials over a field are linear forms
  in characteristic zero and sums of pure p power monomials in characteristic
  p”. Eight hits included MvPolynomial.IsHomogeneous, homogenization, and
  LinearMap.toMvPolynomial_isHomogeneous. None states this classification.
- `loogle`: `MvPolynomial.IsHomogeneous, MvPolynomial.aeval`. Two hits:
  MvPolynomial.IsHomogeneous.aeval and
  Polynomial.homogenize_eq_of_isHomogeneous. Neither classifies additivity.
- `leansearch`: “Classification of homogeneous polynomials satisfying the
  formal identity f(X+Y)=f(X)+f(Y) over a field”. Eight hits concerned
  homogenization, homogeneity, Euler's identity, and polynomial additive-map
  extensionality, not the formal additivity classification.
- `grep`: `additive|IsAdditive|isAdditive`, Mathlib/Algebra/MvPolynomial:
  zero hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf for
  `additive.*[Pp]olynomial|[Pp]olynomial.*additive|IsAdditive|isAdditive`:
  related additive-group constructions, the triangular-coordinates consumer,
  and unrelated transport predicates; no classification theorem.
- Direct rg of the item id in lean/WeilConjectures: no hits.
- Direct rg of `additive_monomial_classification|homogeneous_additive|isAdditivePolynomial`
  in Mathlib, lean/WeilConjectures, and lean/Sheaf: no existing declaration.

Validation: scompile.py compiled both its sandbox view and the installed-module
view successfully, with no errors or unexpected warnings. All variables and
universes are explicitly bound, and `set_option autoImplicit false` enforces
this. Maximum source line length is 87. No STATEMENT-DISPUTED issue was found.

## Second reading by Q127

The dispatcher explicitly forbids starting another agent. This section records
the writer's second pass with the node and module open; the maintainer supplies
the independent delivery review.

Rereading the exact signature against the node confirmed Field k, arbitrary
n>=0, positive d, nonzero f and total-degree homogeneity, the formal identity
in two disjoint tuples, and both directions in both characteristic cases.
The first right side includes both d=1 and the coefficient representation.
The second right side includes an existential nonnegative exponent, the
same exponent in the degree and every pure monomial, and arbitrary coefficients.
There is no prime assumption, algebraic-closure assumption, nonempty-index
assumption, functional substitute for the identity, or restriction on the
field universe. Parentheses keep each characteristic implication outside its
whole equivalence. No mismatch or second-pass edit was needed.
