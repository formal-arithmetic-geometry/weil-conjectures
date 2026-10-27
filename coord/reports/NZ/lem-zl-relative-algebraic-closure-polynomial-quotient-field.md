## Worker report

The module `Sheaf.FieldTheory.RelativeAlgebraicClosurePolynomialQuotientField` states
`Polynomial.irreducible_map_and_isField_quotient_of_isAlgebraic_mem`. Its only proof is `sorry`.
There are no definitions, new nodes, dependency repairs, or statement changes.

Clause-by-clause correspondence:

- The field extension is `{k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]`.
  The structure homomorphism is `algebraMap k K`; the universes are independent.
- Every algebraic element is the image of a base-field element:
  `h : ∀ x : K, IsAlgebraic k x → ∃ y : k, algebraMap k K y = x`.
- The polynomial is `P : Polynomial k`; monicity is `hP : P.Monic`, whose definition is
  `P.leadingCoeff = 1`. Irreducibility is `hPirr : Irreducible P`: nonunit and a unit
  factor in every factorization. Although the general monoid predicate does not include
  nonzeroness as a field, over the nontrivial domain k[X] this implies nonzeroness;
  monicity also excludes zero. Thus the node's explicit nonzero clause is retained.
- The coefficientwise image P_K is the literal term `P.map (algebraMap k K)`.
- Its irreducibility is the first conjunct `Irreducible (P.map (algebraMap k K))`.
- The ideal of all multiples is exactly `Ideal.span {P.map (algebraMap k K)}`;
  `Ideal.mem_span_singleton` identifies membership with divisibility. The quotient is the
  literal `Polynomial K ⧸ Ideal.span {P.map (algebraMap k K)}`.
- The nonzero field assertion is `IsField` of that quotient, using its existing commutative
  ring structure. `IsField.exists_pair_ne` includes nontriviality; its other fields assert
  commutativity and existence of multiplicative inverses of all nonzero elements. This
  avoids choosing an unrelated field structure on the quotient type.
- Exactly one point of the affine spectrum is
  `Nonempty (Unique (AlgebraicGeometry.Spec (CommRingCat.of (...))))`. The scheme-to-type
  coercion is its underlying topological space. `Unique` includes both a point and
  equality of every point to that point, and `Nonempty` turns the structure into a proposition.
- Irreducibility is `IrreducibleSpace` of the same affine spectrum, including nonemptiness.
- There is no separability, finite-dimensionality, finite-type, finite-generation,
  characteristic, degree, or universe-equality assumption.

Dependency declarations read in full in the local live-project Mathlib source:

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`.
- `def-weil-algebraic-element`: `Mathlib.RingTheory.Algebraic.Defs`, `IsAlgebraic`.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  `Mathlib.Algebra.Polynomial.Degree.Defs`, `Polynomial.Monic`, `leadingCoeff`.
- `def-weil-coefficientwise-ring-hom-map`: `Mathlib.Algebra.Polynomial.Eval.Defs`,
  `Polynomial.map`. Only its polynomial clause is relevant here.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`, `IsIrreducible`,
  `irreducibleComponents`, `IrreducibleSpace`. The node includes the notion of an irreducible
  space; its recorded file provides it directly, so no repair is necessary.

The proof-dependency modules are imported privately: `Mathlib.RingTheory.Polynomial.IsIntegral`
for `Polynomial.isIntegral_coeff_of_dvd` (lem-zl-monic-divisor-algebraic-coefficients),
`Mathlib.RingTheory.Algebraic.Integral` for `IsIntegral.isAlgebraic`,
`Mathlib.Algebra.Polynomial.FieldDivision` and `Mathlib.RingTheory.PrincipalIdealDomain`
for the polynomial Euclidean/PID instances (lem-pur-polynomial-field-pid). The quotient-field
leaf `Ideal.Quotient.field` is in the already public-imported
`Mathlib.RingTheory.Ideal.Quotient.Basic`, which supplies the actual quotient used in the statement.
All five proof steps are reproduced in the theorem docstring with their dependency IDs.

Source read: `literature/stacks-project/algebra.tex`, Tag 037P, lines 11297 onward,
and Tag 00H6, lines 8433 onward. The source descends coefficients of monic factors; this
argument does not require the separability used elsewhere in its geometric application.
The existing project theorem `AlgebraicGeometry.geometricallyIrreducible_of_isAlgebraic_mem`
in `Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible` is the downstream geometric
result, not this polynomial/quotient assertion.

Edge cases checked mathematically before writing:

- K = k and a linear polynomial: the quotient is k with its single-point spectrum.
- P = 0 and constant monic P = 1 are excluded by monicity and irreducibility respectively.
- In characteristic p, k = F_p(s), K = k(t), P = X^p - s: the inseparable irreducible
  polynomial is covered; no separability has been silently imposed.
- Arbitrary transcendence degree, including an infinite transcendental family, is permitted.
- The no-new-algebraic-elements hypothesis is essential: Q inside Q(i) and P = X^2 + 1
  would otherwise fail. The zero quotient and empty spectrum are excluded by the conclusions.

Searches (run with the prescribed msearch.py wrapper):

- LeanFinder: `An irreducible polynomial over a relatively algebraically closed subfield
  remains irreducible over the larger field`. Eight hits, including Gauss's lemma requiring
  `IsFractionRing` and the purely inseparable extension lemma requiring a separable polynomial.
  No exact match.
- Loogle: `Polynomial.map, Irreducible`. Twelve hits; the monic map lemma goes in the reverse
  direction, Gauss lemmas need a fraction field, and other hits concern composition or
  Eisenstein. No exact match.
- grep: `irreducible.*(algebraic|algebraically)|IsRelativelyAlgebraicallyClosed|isRelativelyAlgebraicallyClosed`.
  Three unrelated hits in Differential/Basic and AlgebraRepresentation/Basic. No exact match.
- LeanSearch: `If every algebraic element of K over k belongs to k then an irreducible
  polynomial over k stays irreducible over K`. Eight hits, again the separable/purely
  inseparable result and fraction-field Gauss lemma, not this result.
- rg of `lean/WeilConjectures/FieldTheory`, `lean/Sheaf/FieldTheory`, and then both full trees
  for relative algebraic closure and mapped irreducibility found the downstream geometric
  theorem and parameter-specific binomial lemmas, not the full assertion. grep for the
  item's exact ID in `lean/WeilConjectures` had no hits. The proposed full declaration name
  has no hit in Mathlib, either project tree, or `dag/lean_names_upstream.json`.

Validation: scompile.py compiled this module in sandbox mode and library mode, cleanly
(24.5 s and 4.4 s). All universes and variables are explicitly bound. No faults or disputes.
The supplied CompactObject example is now a withdrawn empty module; current nonempty
stage-2 FieldTheory modules were also inspected for the required module-mode header.

## Second reading by NZ

Author's separate source-to-signature check, not an independent review: reopened the node and
compared its extension and closure hypothesis with the binders, its monic irreducible P with
hP/hPirr, and its four conclusions with the conjunction. Checked that the ideal is generated
by the mapped polynomial, the field predicate uses the original quotient ring operations,
and both topology assertions concern exactly its Spec. No discrepancy found and no change
needed. The maintainer supplies the independent review under the dispatcher's direct-delivery
protocol; no other agent was started.
