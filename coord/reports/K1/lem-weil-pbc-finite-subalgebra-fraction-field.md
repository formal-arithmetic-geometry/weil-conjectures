## Worker report

The module `Sheaf.RingTheory.FiniteSubalgebraFractionField` states
`MvPolynomial.exists_finite_subalgebra_fraction_field`, with proof `sorry`.
No definitions, extra nodes, dependency replacements, or statement corrections are needed.
The declaration docstring contains all five steps of the DAG's denominator-clearing proof.

The source is Stacks Project, More on Algebra, Tag 07PR, proof, the finite algebra model
paragraph: https://stacks.math.columbia.edu/tag/07PR . The local literature file was absent,
so the source was read on that official page. It supplies the finite model assertion;
the node's proof_origin correctly marks the supplied denominator-clearing proof as agent-written.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- Characteristic p > 0: `(p : ℕ) [CharP k p] (hp : 0 < p)`.
  Primality need not be added: positive characteristic of a field is prime.
- n,m ≥ 0: `(n m : ℕ)`, including zero.
- A = k[[x_1,...,x_n]][y_1,...,y_m]:
  `MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)`, written explicitly throughout.
  `MvPowerSeries` is the recorded power-series dependency. `MvPolynomial` is Mathlib's
  finite-monomial representation of the same iterated polynomial ring described by the
  polynomial dependency and explicitly discussed in proof step 1. Its coefficients are
  finitely supported functions on exponent vectors, with convolution multiplication.
  It does not introduce another mathematical notion or a private copy. The univariate
  `Polynomial` representation agrees via `MvPolynomial.uniqueAlgEquiv`, and induction
  over the finite variable set identifies this with an iterated univariate polynomial ring
  via `MvPolynomial.finSuccEquiv` (Equiv.lean:650) and `isEmptyAlgEquiv` (line 266).
- A is an integral domain: the first conclusion is `IsDomain A`, not an added hypothesis.
- K = A_(0), its fraction field: `(K : Type v) [Field K] [Algebra A K]`
  and `[IsLocalization.AtPrime K (⊥ : Ideal A)]`. The recorded localization dependency
  supplies this abstract localization class as well as the concrete quotient carrier.
  Quantifying over a model of the localization avoids selecting an unnecessary quotient
  carrier; at zero, the denominators are precisely the nonzero elements of the domain A.
- M/K a field extension: `(M : Type w) [Field M] [Algebra K M]`.
- M is a finitely generated K-module: `[Module.Finite K M]`.
- The map A → M is the stated composite A → K → M:
  `[Algebra A M] [IsScalarTower A K M]`. These express the already specified structural
  map, rather than adding a restriction to the field extension.
- B ⊆ M a subring containing A: `∃ B : Subalgebra A M`.
  A subalgebra contains the image of `algebraMap A M` and, over a ring, is closed under
  addition, multiplication and negation. It is exactly a subring containing A.
- B finitely generated as A-module: `Module.Finite A B`, using its canonical subtype module.
- M is B's fraction field: `∀ z : M, ∃ b s : B, (s : M) ≠ 0 ∧
  z = (b : M) / (s : M)`. The field is M itself and the inclusion is the actual subtype
  inclusion. This is precisely the parenthetical fraction criterion in the node.

Dependency declarations read and used:

- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`,
  `Mathlib.RingTheory.MvPowerSeries.Basic`, via NoZeroDivisors import.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`, read;
  the item's finite-variable application is represented by Mathlib's `MvPolynomial`
  from `Mathlib.Algebra.MvPolynomial.Basic`, not redefined. Both underlying coefficient
  definitions and their docstrings were inspected.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` and
  `IsLocalization.AtPrime`, `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  The dependency's other clauses `Ideal.ResidueField` and `Ideal.Fiber` were also read;
  they are not used by this item.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, transitively imported.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.
- `Subalgebra`, `Mathlib.Algebra.Algebra.Subalgebra.Basic` (transitive import), inspected
  to verify image containment and its subring meaning.

Edge cases checked before writing: n = 0 (power series over the empty variable set are k),
m = 0 (polynomials over the empty variable set are the coefficient ring), and n = m = 0
(A is k, and B = M works). The extension M = K also works with B the image of A.
No separability or perfectness is assumed; purely inseparable extensions are included.
The fraction condition includes z = 0, represented by b = 0 and s = 1.
The zero ring cannot occur because k is a field. Universes u, v, w are independent and
explicit, and all variables are explicitly bound. No statement dispute or node fault found.

Searches for an existing full statement (2026-10-11):

- msearch.py LeanSearch: `finite extension of fraction field admits finite subalgebra
  with the extension as fraction field`. Service unavailable: Internal Server Error;
  no verdict inferred from the failed search.
- msearch.py LeanFinder: `finite extension of the fraction field of a domain has a finite
  subalgebra whose fraction field is the extension`. Eight hits included
  `IsIntegralClosure.isFractionRing_of_finite_extension`, its integralClosure variant,
  `IsIntegralClosure.finite`, and finite-dimensional fraction-field results. These are
  ingredients or impose integrally closed/Noetherian/separability hypotheses; none is
  this full existence statement.
- msearch.py Loogle: `IsFractionRing, Module.Finite, Subalgebra`. Five hits concerned
  discriminants, coprime different ideals and Dedekind domains; no match.
- msearch.py grep in RingTheory: `finite.*subalgebra|fraction field.*finite extension|
  exists_integral_multiples`. Hits included `exists_integral_multiples`,
  `Algebra.IsAlgebraic.exists_integral_multiples` and subalgebra finiteness API;
  these are ingredients, not the combined statement.
- rg over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`:
  `finite.*subalgebra|fraction field.*finite extension|exists_integral_multiples|
  lem-weil-pbc-finite-subalgebra-fraction-field`. No declaration matching this node;
  the PolynomialFormalFiber module mentions the construction only in its proof docstring.
- rg over Mathlib, source Lean, Sheaf and `dag/lean_names_upstream.json` for
  `exists_finite_subalgebra_fractionField|exists_finite_subalgebra_fraction_field`:
  no existing declaration with the proposed name.
- rg over DAG nodes for multivariate polynomial / MvPolynomial found related uses and
  the polynomial-domain node, rather than a different required definition.

Validation: scompile.py compiled the module on the server with exit code 0 and no warnings
(after adding the explicit CharP.Defs import). The final dry run is recorded below.


## Second reading by K1

I independently opened the delivered node and module, all five statement-dependency
nodes and their recorded Mathlib declarations. No mismatch was found; the Lean file
and node record are unchanged. Only this second-reading report was added.

Source check: the repository has no local Stacks checkout. I read the official
[Tag 07PR](https://stacks.math.columbia.edu/tag/07PR), then fetched the upstream
`more-algebra.tex` into this sandbox's scratchpad and read
`lemma-helper-G-ring`, including the whole proof (lines 12306–12361).
The source uses a positive-characteristic field, the power-series polynomial ring,
its fraction field, and a finite intermediate extension M in a purely inseparable
extension. It asserts the finite A-subalgebra model before continuing with additional
purely inseparable arguments. The node states the model construction for arbitrary
finite M/K; its five-step denominator-clearing proof needs no inseparability and is
correct in that generality. The prime and completion in the surrounding source are
not hypotheses for this model construction. The node is not being corrected.

Object, hypothesis and conclusion list, matched independently to Lean (H3):

1. Field k: `(k : Type u) [Field k]`. Verdict: exact; nontriviality is part of Field.
2. Characteristic p > 0: `(p : ℕ) [CharP k p] (hp : 0 < p)`.
   Verdict: exact. No perfectness, algebraic closure or separability is imposed;
   primality follows from the field and positive characteristic.
3. Nonnegative n and m: `(n m : ℕ)`. Verdict: exact, with both zero cases included.
4. Formal power-series coefficient ring: `MvPowerSeries (Fin n) k`.
   Verdict: exact. Basic.lean:86 defines all functions from exponent vectors to k,
   not restricted/convergent power series. Fin n exponent vectors are precisely N^n.
5. Polynomial ring A in m variables over that coefficient ring:
   `MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)` everywhere in the signature.
   Verdict: exact. Basic.lean:82 uses finitely supported coefficients on exponent
   vectors. I also opened the dependency's `Polynomial` at Basic.lean:74 and the
   signatures of `MvPolynomial.finSuccEquiv` (Equiv.lean:650) and `isEmptyAlgEquiv`
   (Equiv.lean:266): the finite-variable presentation is the iterated univariate
   polynomial ring, preserving the coefficient algebra. No private notion is defined.
6. A is a domain: the first conjunct `IsDomain (MvPolynomial ... ...)`.
   Verdict: stated as a conclusion. No IsDomain assumption was added to the binders.
   The imported NoZeroDivisors instances establish the zero ideal's primality when
   the localization binder is elaborated; this introduces no independent hypothesis.
7. K = A_(0), the fraction field: `(K : Type v) [Field K] [Algebra A K]` and
   `[IsLocalization.AtPrime K (⊥ : Ideal A)]`, with A expanded verbatim in Lean.
   Verdict: exact up to the usual unique algebra isomorphism. AtPrime.Basic.lean:52
   abbreviates localization at the prime complement, here A minus zero. The Field
   structure records what A_(0) is, rather than assuming an arbitrary field map.
8. Finite field extension M/K: `(M : Type w) [Field M] [Algebra K M]` and
   `[Module.Finite K M]`. Verdict: exact. Algebra.Defs.lean:95 supplies the ring map;
   Finiteness.Defs.lean:117 requires the top submodule to be finitely generated,
   whose definition at line 40 is the span of a finite set.
9. The specified inclusion A into M: `[Algebra A M] [IsScalarTower A K M]`.
   Verdict: compatibility expresses the composite A → K → M, not a stronger
   extension hypothesis. For any given K/M extension the composite supplies these
   structures. Domain localization and the field map ensure injectivity.
10. Existential subring B of M containing A: `∃ B : Subalgebra A M`.
    Verdict: exact. Subalgebra.Basic.lean:29 includes `algebraMap_mem'`; over a ring
    its canonical ring structure also includes additive inverses. The actual ambient
    field is M, and the map from B is its subtype inclusion.
11. B finite as A-module: `Module.Finite A B`. Verdict: exact, using the canonical
    subtype module and the structural map specified above.
12. M is the fraction field of this same B: `∀ z : M, ∃ b s : B,
    (s : M) ≠ 0 ∧ z = (b : M) / (s : M)`.
    Verdict: exactly the node's explicit parenthetical fraction criterion. A subring
    of the field M is a domain, and subtype injectivity identifies nonzero s in B
    with its nonzero image. Quantifier order is B first, then every z, then b and s;
    no separately chosen field or unconnected embedding occurs.

Edge cases: n = 0 gives the coefficient field (the zero exponent vector is the only
one); m = 0 gives the coefficient ring; n = m = 0 gives A = k and B = M is finite.
M = K admits the image of A as B. z = 0 is 0/1, and all denominators are required
nonzero. There is no zero-ring case for a field. Characteristic zero is excluded by
the node itself; positive characteristic, including imperfect fields and inseparable
extensions, is covered. No schemes or separate index sets appear. Independent explicit
universes u, v, w allow arbitrary universe levels of k, K and M. All variables and
universes are bound; there is no quantified test family whose universe could make
an assumption vacuous.

Independent H4 searches, with queries differing from the worker's:

- LeanSearch via msearch.py: `finite module subring of algebraic field extension with
  prescribed field of fractions`. Service unavailable (Internal Server Error);
  no absence verdict inferred from it.
- LeanFinder: `finite integral model in an algebraic extension generated by clearing
  denominators`. Eight hits: integral-multiple/basis lemmas, integrality from finiteness,
  integral-closure finiteness and Noether normalization; no combined model statement.
- Loogle: `IsFractionRing, Subalgebra`. Twelve hits: integralClosure fraction-ring
  theorems and localization subalgebra results. I opened Localization/Integral.lean
  lines 380–430: the fraction-field assertions for integral closures do not assert
  module finiteness; integral-closure finiteness needs additional hypotheses.
- rg over Mathlib RingTheory/Algebraic, Localization and IntegralClosure for
  `finite.*model|exists.*subalgebra|isFractionRing_of_finite_extension|
  finite_adjoin_of_finite_of_isIntegral` found the known separate ingredients.
- rg over source WeilConjectures, repository lean/Sheaf and upstream-name records for
  `fraction.*subalgebra|finite.*model|exists_finite_subalgebra_fraction_field` found
  unrelated geometric models and proof references. I opened the apparent affine
  model hit, AlgebraicGeometry/Curve/Affine.lean:68: it is a normalization theorem
  for smooth curves over an algebraically closed field, not this ring statement.
  No existing declaration realizes the full node.

H5–H9: there is one theorem, with only `by sorry`, and no definitions or other proofs.
Both docstrings name 07PR and the exact blueprint id. The declaration docstring
faithfully carries all five proof steps, including the common denominator, integral
finite generators and the final numerator/denominator construction. Imports supply
CharP, MvPolynomial, power-series domain instances, localization and module finiteness;
all are used. Namespace and path follow the conventions, with no Sheaf declaration
prefix. There are no new nodes or dependency modules to review under H12/H13.
No statement correction or citer-verdict review is required.

Validation: scompile.py on the delivered module returned exit code 0, compiled in
1.3 seconds, with no warnings. A literal signature comparison confirms lean.statement
is verbatim the theorem signature before `:= by`; all source lines are at most
100 characters. Nothing mathematically correct was rewritten.
