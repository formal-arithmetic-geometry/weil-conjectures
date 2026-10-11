## Worker report

The module `Sheaf.RingTheory.SeparablePolynomialQuotientReduced` states
`Polynomial.isReduced_quotient_of_separable`.  It uses Mathlib's `Field`,
`Polynomial` (`E[X]`), `Polynomial.Separable`, `Ideal.span`, and natural powers.
For a field `E`, polynomial `Q`, and hypothesis `hQ : Q.Separable`, the
conclusion quantifies every polynomial `g` and natural number `m`, assumes
`1 ≤ m`, and assumes `g ^ m ∈ Ideal.span ({Q})`; it concludes
`g ∈ Ideal.span ({Q})`.  This is exactly the stated reducedness criterion for
`E[X]/(Q)` and includes constant and zero-polynomial cases through
`Polynomial.Separable`.

Dependencies used:

- `def-weil-field`: Mathlib `Field` class.
- `def-weil-polynomial-ring`: Mathlib `Polynomial` notation `E[X]`.
- `def-pc-separable-polynomial`: Mathlib `Polynomial.Separable` (the recorded
  definition is `IsCoprime Q Q.derivative`, equivalent to the Bezout clause).

Edge cases checked: `m = 0` is excluded by `1 ≤ m`; `m = 1` is included;
separable nonzero constants are permitted and the zero polynomial is excluded
by separability.  The ideal is the principal ideal `Ideal.span ({Q})`, so the
statement covers arbitrary `g` and zero classes in the quotient.

Searches made: `msearch.py ... leanfinder "quotient of polynomial ring over a
field by a separable polynomial is reduced"` (found only ingredients);
`msearch.py ... loogle "IsReduced (AdjoinRoot _)"` (none);
`msearch.py ... grep "isRadical_iff_quotient_reduced|Squarefree.isRadical|AdjoinRoot.*reduced"`
(found the four-declaration Mathlib chain); `rg` over `WeilConjectures/` and
`lean/Sheaf/` (no existing declaration of this statement).  Mathlib's
`Polynomial.Separable.squarefree`, `Squarefree.isRadical`,
`isRadical_iff_span_singleton`, and `Ideal.isRadical_iff_quotient_reduced` are
proof ingredients but no single existing declaration matches this node.

## Earlier second reading (a previous round; superseded)

I read the node statement and its source (Stacks Algebra, Tag 030U, line
10182).  The field hypothesis is rendered by `[Field E]`; the polynomial ring
and separable polynomial are rendered by `E[X]` and `Q.Separable`; the
principal ideal is exactly `Ideal.span ({Q})`.  The node's two conclusion
clauses are rendered in order: `m ≥ 1` is `1 ≤ m`, and divisibility of the
power and of the base are the two ideal-membership implications.  No object,
hypothesis, or clause is added or omitted.  The dependency records were read:
`Field`, `Polynomial`, and `Polynomial.Separable` are the Mathlib declarations
used directly.  The edge cases listed above were checked against the source
statement.


## Second reading by G1

Independent reading of the node, its two proof steps, the sandbox module, and
Stacks Algebra Tag 030U (algebra.tex lines 10150–10190, read over ssh on the
server because literature is not installed in this read-only clone). The source
introduces a field F and a separable polynomial P and concludes that F[T]/(P)
is a finite product of fields. This node isolates the reducedness consequence;
its abstract field E and arbitrary separable Q require no extra hypotheses from
the preceding tensor-product argument.

Objects, hypotheses and conclusion clauses, checked individually:

- Field E: `(E : Type u) [Field E]`; exact. Read `Field` in
  Mathlib.Algebra.Field.Defs:180: it extends CommRing and DivisionRing, including
  nontriviality and inverses. This is def-weil-field's Mathlib match.
- Polynomial ring E[T]: `E[X]`; exact. Read `Polynomial` in
  Mathlib.Algebra.Polynomial.Basic:74 and its notation: the carrier wraps
  finitely supported natural-number coefficients, as def-weil-polynomial-ring
  records. The indeterminate's name changes no object.
- Q in this ring: `(Q : E[X])`; exact, without monicity, positive degree or
  irreducibility assumptions.
- Separability, including the displayed Bezout identity: `(hQ : Q.Separable)`;
  exact. Read Mathlib.FieldTheory.Separable:44–52 and
  Mathlib.RingTheory.Coprime.Basic:45: this is literally the existence of U,V
  with U*Q + V*Q.derivative = 1, the def-pc-separable-polynomial match.
- Principal ideal (Q): `Ideal.span ({Q} : Set E[X])`; exact, the ideal generated
  by the singleton Q, with no second/private notion of the ideal or quotient.
- Arbitrary g and positive integer exponent: `∀ (g : E[X]) (m : ℕ), 1 ≤ m →`;
  exact. Positive integers and positive naturals give the same polynomial powers;
  using naturals excludes only undefined negative powers and zero, already
  excluded by the node's m ≥ 1.
- Power in the ideal: `g ^ m ∈ Ideal.span ({Q} : Set E[X]) →`; exact.
- Base in the ideal: `g ∈ Ideal.span ({Q} : Set E[X])`; exact. This is precisely
  the node's explicit reducedness criterion. Every quotient class has a
  polynomial representative, so this criterion includes all nilpotent classes;
  it neither weakens nor strengthens IsReduced of the quotient.

Edge cases: Q = 0 is excluded by Bezout over a nontrivial field; every nonzero
constant Q is allowed, giving the zero quotient ring, which is reduced. g = 0
is allowed. m = 0 is excluded and m = 1 included. No characteristic assumption
is present, including characteristic 2 (the derivative argument still has H
as a factor). `universe u` is bound and arbitrary; E[X] uses the same universe.
No index set or scheme occurs, so empty-index/empty-scheme cases do not apply.
No additional instances, finiteness assumptions or unbound variables occur.

Independent searches used different terms from the first worker:
`msearch.py ... leanfinder "A coprime polynomial and its derivative generate a
radical principal ideal"` returned separability definitions and derivative
lemmas, but no matching theorem; `msearch.py ... loogle
"Polynomial.Separable, IsReduced"` returned zero hits. `rg` over pinned Mathlib,
WeilConjectures and repository lean/Sheaf for `separable.*reduced`,
`reduced.*separable`, `squarefree.*quotient`, `quotient.*squarefree`, and
`coprime.*derivative` found surrounding field/tensor results and ingredients,
not this statement. Searched dag/lean_names_upstream.json for separable and
Reduced and checked the proposed full name in the source and project: no name
collision. Read Squarefree and Squarefree.dvd_pow_iff_dvd at
Mathlib.Algebra.Squarefree.Basic:42 and :168: these are the node's proof leaf,
not a theorem already stating this entire separability/ideal implication.
Together with the first worker's searches, no existing declaration was found.

Mismatch and repair: H8, the docstring summarized rather than carried the
node's complete proof. Expanded it to the square-divisor/derivative calculation,
Bezout unit argument, constant/zero cases, named proof dependency, divisibility
step, and vanishing of every nilpotent quotient class. H9, removed unused
imports Mathlib.Algebra.Squarefree.Basic and
Mathlib.RingTheory.Ideal.Quotient.Nilpotent; the signature requires only
Mathlib.FieldTheory.Separable. No mathematical signature or node change was
needed. There are no new nodes or dependency modules and no statement_change.
The sole theorem remains `by sorry`, and there are no definitions or hollow data.

Validation: scompile.py G1 lem-weil-pbc-separable-polynomial-quotient-reduced
compiled the repaired 49-line module cleanly (exit 0, 1.3 seconds). Checked the
node's lean.statement against the file by exact string equality, from theorem
to the text before :=; it is unchanged and identical.
