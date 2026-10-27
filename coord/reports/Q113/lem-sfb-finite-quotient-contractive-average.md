# Stage-1 report: lem-sfb-finite-quotient-contractive-average

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-contractive-average.json`: statement, split; six explicit elementary proof steps. The statement, existing source and ancestry, and inherited searches are retained.
- `citations.json`: one verbatim statement excerpt for every citation in the six steps.
- `searches.jsonl`: the unmodified output records of msearch.py invocations.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. There is no prior item copy or report in this sandbox to replace.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint identifier, contractive/contracting terminology, and averaging. The nearby discrete-module Procyclic averaging concerns lifting finite torsion invariant elements, and the Artin–Schreier averages concern sheaf projectors; neither states this item's nonarchimedean supremum bound and quotient-refinement assertions. No project declaration states every clause, so no attachment is claimed.

## WANTED

WANTED: a published reference for normalized nonarchimedean scalar averaging on the union of open-normal quotient-function spaces of a prime-to-ell profinite group, for lem-sfb-finite-quotient-contractive-average. The current blueprint paragraph (3) is the application context, not a proof of this auxiliary. The proof is explicitly agent-written.

## Problems found and changes

The item was statement-only and is mathematically correct as written. No statement dispute, change of coefficients, or route change is needed. Its recorded unit identifier `sk-thm-sf-ctf-stability` resolves to the older six-functors unit; I read that unit and also the actual current six-functors-basics unit and direct-images proof under `literature/blueprint/latest/`. The latter's paragraph (3) treats open and proper direct images but contains no scalar averaging proof. I therefore do not attribute the new elementary proof to that text. The existing null nearest blueprint ancestor was confirmed by `tools/blueprint_refs.py ancestor`; it is retained, with an exact contextual place and its existing via list. No chapter or unit record is changed.

The proof does not manufacture a new node for the finite-group average, quotient fibers, finite sums, or a clause of the item. It writes the actual fiber bijection, finite partition count, common-refinement comparison, and ultrametric induction in the item's steps. These are elementary finite arguments, not black-box lemmas. Completeness is never used.

## Search and duplicate checks

Searched the whole DAG by averaging, ultrametric/nonarchimedean, finite-sum, open-subgroup and norm terminology, and read the nearby scalar-integral and scalar-cochain statements and their existing use of this item. Whole-blueprint searches with `tools/blueprint_refs.py search` used `averag`, `ultrametric` and `finite quotient`; there is no blueprint statement equivalent to the item. No new node is proposed, so there are no tag-sharing new/existing pairs to justify.

The inherited Mathlib search records and their actual hit lists were read and preserved. Fresh msearch.py searches used LeanFinder in two phrasings, Loogle for `"averageMap"`, LeanSearch for compatible finite-quotient averages, and grep for prime-to-p norm facts and profinite averaging. Their results are recorded exactly, with no failed service called a negative match. Read Mathlib/RepresentationTheory/Invariants.lean:129–147: Representation.averageMap is a projection of a finite group representation, not the compatible contraction on this union of function spaces. Read Mathlib/NumberTheory/Padics/PadicNumbers.lean:944–959: Padic.norm_natCast_eq_one_iff confirms the elementary valuation-zero denominator calculation; the proof itself derives it from the cited definition of the rational valuation. Neither result is a match for the whole item. Haar hits are real-valued measure theory; LocallyConstant.discreteQuotient is factorization, not averaging; Finset.expect_nbij reindexes a bijection and does not give the equal-fiber refinement argument.

## Not duplicates

No new nodes. In particular I did not reuse `lem-exc-etale-open-subgroup-quotient-finite-discrete` as if it stated arbitrary compact groups: its statement specializes to an absolute Galois group. Step 1 instead proves its needed elementary finite-subcover argument directly. `lem-sfb-finite-quotient-fiber-product` concerns compatible partitions of a topological fiber product and says neither finite-group averaging nor equal-fiber summation.

## Review by Q113

I read the current blueprint direct-images statement and proof and the applicable chapter and unit records. The source only motivates the scalar auxiliary; the six steps are my argument. There are no new nodes or unconsulted external references. I checked delivery-errors B through E against the item and every actual citation.

Step 1 uses no cited theorem: translated open cosets give an open cover, compactness gives finitely many cosets, and inverse images of subsets are unions of cosets. This also proves continuity of every descended function. Nonemptiness comes from the identity. Step 2 explicitly intersects two open normal subgroups, writes the quotient maps, and expresses a linear combination on their common quotient. Normality is essential to the displayed left and right quotient multiplications and is an item hypothesis.

Step 3 cites only `def-weil-l-adic-numbers`; I opened its full statement. Its characteristic-zero assertion is exactly what is used for cancellation of positive integer denominators after the isometric field embedding. The step separately proves equal fiber sizes by the map uV to kuV with its inverse and partitions the finite sums. No cardinality theorem or invariance theorem is silently cited. In step 4, equality of the two lifted functions follows by evaluating at each lift under the surjective common quotient map. Step 3 then gives independence. Linearity is written on that common quotient, rather than assumed of a not-yet-well-defined operator.

Step 5 again cites `def-weil-l-adic-numbers`, this time its explicit rational valuation formula and absolute value formula. A positive integer prime to ell has valuation zero, so its norm and its inverse's norm are one in B. The quoted definition actually states this formula; the isometry is a hypothesis on B. The strong triangle inequality is also a hypothesis, and the finite-sum estimate is proved by induction, including the empty partial sum. Because the quotient is finite and nonempty, its maximum exists and surjectivity identifies it with the actual supremum of f. No completeness or general function-space extension theorem is needed. Step 6 writes the two permutations and inverses and reindexes the finite sums, then calculates the average of one. The only citation there is the universe convention, whose entire statement is quoted in citations.json; no algebraic property is inferred from it.

Small cases checked: K trivial or U=K gives the one-point average and every constant; V=U gives fiber size one; f=0 gives the zero bound; an intersection equal to either subgroup gives the same comparison; any positive prime-to-ell finite group and finite product of such groups obey the same count; noncommutative quotient groups still have both multiplication permutations. Groups and their quotients cannot be empty. The induction uses a nonnegative bound for its empty partial sum. No step is longer than 2000 characters, and no step hides an identification of derived objects or an analytic limit. All proof dependencies are exactly the union of step uses, and citations.json contains one verbatim quote for each use. No SGA source is used.

## Unfinished work

None for this one-level stage-1 split. No Lean was written and no compiler, Lake or build tool was run. The required server dry run and direct delivery are performed after this report is written.
