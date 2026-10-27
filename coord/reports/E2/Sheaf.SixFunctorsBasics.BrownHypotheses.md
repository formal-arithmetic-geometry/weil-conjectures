## What changed

Proved three additional conditional results in the item module:
`CategoryTheory.BrownHypothesesFor.eventually_hom_single_shift_eq_zero`,
`CategoryTheory.BrownHypothesesFor.exists_uniform_hom_single_shift_bound`, and
`CategoryTheory.not_brownHypothesesFor_of_unbounded_ext`.

Brown compactness forces eventual vanishing along every sequence F_n[0][n], even
when the heart object varies with n. A choice argument then gives a bound uniform
over every heart object whose degree-zero image belongs to the localizing closure.
Unbounded Ext into such heart objects therefore contradicts the Brown bundle.
This strengthens the existing diagnostic, which required nonzero maps to every
positive shift of a single heart object. The existing positive-Ext theorem now
follows by specializing the varying-heart bound to a constant sequence.

The proof generalizes the source-library finite-support argument and uses its
proved degreewise-disjoint product-coproduct construction. It explicitly restricts
both universal properties to the actual full localizing subcategory. The original
theorem signatures, definition bodies, public imports and visibility stay unchanged.
No new imports or source-library modifications are needed. Added two proved nodes,
updated the positive-Ext node's proof route, and recorded the strengthened diagnostic
in the item node. The unit route and all original attachment and dependency fields
are preserved.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, retaining its original disputed statement.
The three new theorems above and the shortened original positive-Ext proof are complete.
This is a proved necessary compactness bound and diagnostic packet, not a proof or
holed decomposition of the original arbitrary-field assertion.

The unmodified baseline compiled via the prescribed lcompile.py in 47.1 seconds,
exit 0. The final edited module compiled in 48.2 seconds, exit 0, with no warnings.
A source-parser comparison confirms every original declaration signature and
every non-theorem body is unchanged; the import list is identical. The delivery
tool performs the required axiom probe and consumer/interface checks.

A separate source-containing axiom probe compiled in 32.9 seconds, exit 0.
For all three new declarations and the shortened positive-Ext obstruction,
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
None depends on the original holed assertion.

The first required deliver3.py attempt returned exit 75 after its managed wait:
`DELIVERY BUSY: 12 deliveries are running on this machine; retry in a few minutes`.
It reached neither preflight nor push. The verified packet is preserved for retry;
no launcher script, budget metadata or capacity setting was modified.

## No longer needed

No imports, modules, declarations or original item dependencies are removed.
The positive-Ext obstruction's direct product-coproduct construction is replaced
by the varying-heart theorem, which still uses the finite-support theorem and the
localizing-closure API. Its node now records that direct dependency. All geometric
finite-field compactness and smallness imports remain used in the original assembly.
No quarantined or currently unimported parent is treated as withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original theorem asserts compactness over an arbitrary
positive-characteristic field. The standing setting explicitly adds no further field
hypothesis. The available compactness inputs require a finite-field datum, a finite
or separably closed field, or a separate Ext bound. Finite type alone supplies none
of these. The admissibility predicate also contains an all-continuous-map
algebraic-closure coefficient absent from the six-case finite-field theorem.
The supported finite-field assembly therefore cannot prove the original claim.

The existing diagnostic uses algebraicClosure(F_3)(t_1,t_2,...) and constant F_2:
iterated Kummer symbols provide nonzero cohomology in arbitrarily high degrees.
This packet proves the categorical bound needed to contradict compactness from
such a calculation, allowing the coefficient sheaf to vary. It does not formalize
that field-cohomology calculation and claims no unconditional Lean counterexample.
No unsupported compactness lemma or renamed copy of the original sorry is added.

Edge checks: zero source objects and zero rings make all Homs vanish; zero or
repeated unshifted heart objects are permitted. Degreewise disjointness comes from
the distinct shifts, not distinct heart objects. If no eligible heart object exists,
the uniform conclusion is vacuous with bound zero. The unboundedness criterion
allows gaps and requires actual nonzero maps, so excludes these vacuous cases.
All choices in the uniform argument occur in a proved proposition, not a data
construction from an unproved existence claim. Index universe lifts are explicit.

## New nodes

`lem-sfb-brown-varying-heart-ext-bound` records eventual vanishing for varying
heart objects. It has a complete proof in the item module and no sorry.
`lem-sfb-brown-uniform-heart-ext-bound` records the uniform bound and its unbounded-
Ext contrapositive, both proved. Blueprint and library searches found no duplicate
of these necessary conditional bounds; the blueprint's uniform constructible Ext
results instead prove sufficient geometric vanishing bounds under extra assumptions.

Change record: `coord/changes/E2-brown-uniform-heart-ext-bound.md`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
