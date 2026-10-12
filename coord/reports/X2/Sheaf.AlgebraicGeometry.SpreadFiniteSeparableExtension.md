## What changed

Proved `AlgebraicGeometry.exists_spread_finite_separable_extension` without changing its
signature or public imports. Added the proved module
`Sheaf.AlgebraicGeometry.LocalizedSeparablePolynomialModel` for the coefficient calculation.
The proof imports that module, `Mathlib.FieldTheory.PrimitiveElement`, and
`Mathlib.RingTheory.Etale.StandardEtale` privately.

The construction clears the three polynomials (the minimal polynomial and the two Bezout
coefficients) using `IsLocalization.integerNormalization_spec`. The product of their three
nonzero multipliers is `c`. The image of `A[1/c]` in `L` constructs `S` explicitly; its canonical
map into `K` descends all three polynomials. Their Bezout identity gives coprimality of `f`
and its derivative. The concrete ring `B = Algebra.adjoin S {alpha}` is identified with
`AdjoinRoot f`, yielding finiteness and etaleness. The fraction-field proof lifts `Frac(B)`
into `L` and proves its image contains `K` and the primitive element. Mathlib's spectrum
characterizations and lying-over give the geometric clauses.

Both delivered modules compile with `lcompile.py --all`. No existing module needs adaptation.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.exists_spread_finite_separable_extension`
(node `lem-weil-pbc-spread-finite-separable-extension`).

Also proved `AlgebraicGeometry.exists_localized_separable_polynomial_model`
(node `lem-weil-pbc-localized-separable-polynomial-model`).

Holes closed: 1. Holes added: 0. No sorry remains in either delivered module.
The three local helpers in the item's module and the normalization helper in the new module
are private, fully proved theorems.

## No longer needed

No imports were removed from the original module; its public interface is preserved.
The proof no longer uses `lem-weil-pbc-minimal-polynomial-quotient-field-iso` as a black box:
it constructs the polynomial quotient equivalence directly using `minpoly.dvd` and
`Polynomial.map_dvd_map`. That planned proof dependency is removed from this node.
There is no associated Sheaf module to prune: the former dependency is a Mathlib leaf.
The primitive-element, standard-etale and lying-over nodes remain in the route.
No other planned nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. Step 2's denominator-clearing calculation required
substantial Lean glue, now fully proved. Clearing a Bezout identity directly supplies an
invertible derivative, so no discriminant infrastructure is necessary.

The new lemma does not assume that alpha generates L, or that A is Noetherian. Its fraction
field conclusion is deliberately absent: the original proof supplies it from primitivity.
For edge cases, alpha=0 gives minimal polynomial X and derivative 1, and a degree-one
extension gives B=S. The normalization proof also handles a zero Bezout coefficient because
its multiplier is still selected from the non-zero-divisors. None of these cases is excluded.

The literature text files are not present in this clone. The existing DAG's complete
calculation was read, as were Mathlib's pinned normalization and localization definitions;
Stacks Tags 00UB and 00UC were checked on their official web pages. The coefficient proof
is an explicit agent-written calculation, with no unproved theorem extracted from a source.

## New nodes

`lem-weil-pbc-localized-separable-polynomial-model` is the proved denominator-clearing
calculation in `lean/Sheaf/AlgebraicGeometry/LocalizedSeparablePolynomialModel.lean`.
It creates no new hole. Its source, complete proof, actual searches, and exact Lean signature
are recorded in the node. The blueprint searches for "separable polynomial" and "spread"
found no existing node with this localized polynomial-and-Bezout conclusion. Its nearest
blueprint ancestor is `lem-weil-pbc-finite-pushforward-generic-constructible`; the route inside
unit `sk-prop-sf-cbc` is preserved. There are no interface change records.


## Second reading by X2

1. Interface: PASS. Compared the full item module with the repository using `diff` and
   the delivery declaration parser. The existing theorem signature is byte-identical;
   no declaration or public import was removed or changed. Only its proof, three private
   proved helpers, and three private imports were added. There are no adaptations or
   interface change records.
2. Proof: PASS. Independently compiled both modules with `lcompile.py --all`, without
   errors or warnings. Scratch-copy `#print axioms` checks for both public theorems report
   exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no sorries or forbidden
   declarations. Read the quotient-equivalence, standard-etale, fraction-field, and
   denominator calculations. S is the explicit localization image and B the explicit
   adjoined subalgebra; no data is extracted from an unproved existence theorem.
3. New statement: PASS. There are no split-off holes. The proved coefficient lemma is
   strictly the denominator/Bezout part of the argument, without a primitive-element,
   finite-algebra, fraction-field, or spectrum conclusion. Checked alpha=0, degree-one
   extensions, a base that is already a field, and zero Bezout coefficients: the selected
   multipliers remain nonzero, and no positive-degree or nonzero-coefficient assumption
   is silently introduced. The docstring gives the complete proof and the new node
   records its signature, source, creation and searches. Independent leanfinder search
   for descending a separable polynomial and Bezout relation, loogle search for
   `Polynomial.map, IsCoprime`, and grep search for integerNormalization/commonDenom
   found supporting results rather than the same statement. Searched both library roots
   and read `Algebra.exists_monic_aeval_eq_zero_aeval_derivative_ne_zero` in the upstream
   residue-field module: it changes the primitive element and does not supply the
   localization or descended Bezout relation, so it does not replace this lemma.
4. Route and pruning: PASS. The proof starts with Mathlib primitivity and uses the proved
   coefficient lemma, monic quotient finiteness, standard etaleness, and lying-over.
   Each added private import supplies declarations actually used. The original public
   imports supply the theorem's types and instances. The only removed planned dependency
   is the minimal-polynomial quotient-field equivalence node, which is a Mathlib leaf;
   no Sheaf module is pruned. The unit `sk-prop-sf-cbc` is unchanged (its recorded
   `realized.statement` and `realized.steps` are empty); the finite-algebra spreading
   calculation still implements the same parent-node step and bypasses no unit.
5. Nodes: PASS. Compared the original and delivered node: only `proof`, `proof_deps`,
   and `proof_origin` changed. The listed dependencies are the union of step uses and
   match the primitive-element, coefficient-model, standard-etale and lying-over
   arguments. The new node matches the Lean signature and describes the explicit
   localization-image and three-polynomial normalization construction.

Second reading changed only this report, adding the independent checks and verdicts.
No Lean or node repair was necessary. The existing item's explanatory docstring still
mentions the former discriminant and quotient-field plan; the actual proof and updated
DAG instead use the reported Bezout calculation and direct quotient equivalence.
