# Stage-1 report: lem-trf-sharp-cone-primitive-facet-preparation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-sharp-cone-primitive-facet-preparation.json`: statement, split; no whole-item Mathlib match. The statement, statement dependencies, original provenance and ancestry are unchanged. The proof has eleven steps, with the existing lattice-intersection theorem and finite rational half-space theorem as its only theorem dependencies.
- `citations.json`: six step/node entries quoting the current statements verbatim.
- `report.md`: this report. `searches.jsonl` is the actual search-command log; `prepare.py` records the sandbox preparation.

There are zero new nodes and zero new Mathlib leaves. Elementary computations remain proof steps rather than new tasks. No Lean file, repository file or launcher file was written, and no compiler, Lake or git command was run in the shared repository.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, sharp cones and primitive facets found no declaration stating the item. The two initially tried historical checkout locations were absent; the searches were then performed in the live source path specified by the brief. No claim of completion is based on a sorry declaration or on a Mathlib declaration.

## Literature and wanted sources

I read ILO, *Travaux de Gabber*, Expose VI 1.1--1.8, printed pages 69--70 (PDF pages 75--76), especially the sharp fs monoid and complete models in 1.6. That source supplies the setting, not the auxiliary cone theorem. I also read the retained old steps 1--5 in `coord/reports/Q138/lem-trf-complete-toric-facet-valuations.md`, the statements and proofs of `lem-trf-sharp-cone-lattice-intersection` and `lem-trf-rational-cone-dual-finite`, and the definition statements `def-trf-complete-toric-model` and `def-trf-fs-log-blowup`. The item's proof is explicitly agent-written. It does not attribute its elementary convex argument to ILO or to an unread reference.

WANTED: K. Kato (1994), *Toric singularities*, as already requested by the parent, for the literature proof of the toric divisor theory behind these auxiliary models. No theorem is attributed to that unread source and no download or literature-list mutation was made.

I read the current blueprint `literature/blueprint/latest/` at commit 7284bb09daf97437d544c51882b325f9c52cd345, including the locality proof (1)--(2), and the item's recorded chapter and unit. The log-regular model ancestry already recorded in the item remains intact; this is auxiliary algebra below that route, not a replacement of the unit's proof. The chapter and unit records were not changed. Whole-blueprint searches for facets, half-spaces, primitive normals and saturated monoids found no duplicate imported node. There is no SGA citation.

## What was wrong and what changed

The item was statement-only, not a returned completed split; the sandbox initially contained only dispatcher markers. I copied the item, retained its searches and statement, and recovered the previously retained cone argument from the parent's report. No released stage-1 repair note for this item exists. The existing `lem-trf-sharp-cone-lattice-intersection` already proves all lattice, saturation and pointedness assertions. The existing `lem-trf-rational-cone-dual-finite` gives exactly the finite rational homogeneous inequalities needed next. Recreating either would duplicate a node.

I expanded the old phrase about a rational segment into its coefficients, replaced the unspecified small perturbations by explicit minima of finite positive rational sets, and wrote out the converse classification of every facet. I replaced the shorthand about a gcd and Bezout with the least-positive-image and integer-division argument. Uniqueness uses an actual lattice element of value one, so its proportionality constant is an integer and the image calculation forces it to be one. Finally the lattice witnesses use the already proved lattice intersection, rather than an unjustified claim that a rational vector lies in the monoid.

There is no statement dispute, added hypothesis or weakened conclusion. The convention that pointed means intersection with the negative cone is zero is inherited explicitly from the lattice node; it is not confused with Mathlib's `ConvexCone.Pointed`, which means containing zero.

## Mathlib searches and reuse

I retained the imported 2026-10-22 search entries and ran fresh leanfinder, Loogle, grep and LeanSearch searches using only the mandated `msearch.py` command. I read both natural-language phrasings. The actual log has six fresh queries: two leanfinder phrasings, one Loogle query, two grep queries and one LeanSearch query. All services answered in this run. The hits concerned simplicial-complex facets, convex or generating cones, Presburger linear sets and number-field cones, rather than primitive facet forms of a sharp fs monoid. The only convex-directory grep hit was the introductory discussion at `Mathlib/Geometry/Convex/Cone/DualFinite.lean:22`; reading the whole file showed definitions and dual-finiteness results, not this facet theorem. No search that was not run was added. No new search log was invented for the retained historical entries.

## Not duplicates

No new nodes were created. The lattice-intersection node is reused for its full lattice/cone conclusion, and the rational-dual-finite node is reused for its finite H-cone description. Neither proves the remaining facet enumeration, primitive normalization and lattice witnesses. The existing rational-dual-integral-forms node gives integral inequalities spanning the dual, but not an irredundant facet enumeration; it is unnecessary here. The facet-form and complete-model definitions introduce notions and are not cited as theorems giving facet existence.

## Review by Q78

I checked the statement against the retained cone proof and read the source setting just described. I opened the complete statement of every cited node, rather than relying on its title or proof. The only substantive theorem applications are steps 1 and 2: both their statements have precisely the hypotheses in force. All other steps write their rational arithmetic, finite-sum or integer-division argument explicitly. No separate unproved polyhedral theorem or primitive-normal theorem is hidden behind a definition citation.

Step 1 uses `lem-trf-sharp-cone-lattice-intersection`: the monoid is finitely generated, integral, saturated and sharp, exactly as that node requires. Its clauses (a)--(c) supply a finite free group embedded in its rationalization, a spanning pointed rational cone and the equality with the monoid. The facet definition in `def-trf-complete-toric-model` requires a nonzero rational linear form, so there are no facets when V is zero. Choosing monoid generators uses the actual finite-generation hypothesis; their rational cone is the original cone by expanding a nonnegative combination.

Step 2 uses `lem-trf-rational-cone-dual-finite`. The finite-dimensional space and finite generating list were established first; that theorem permits empty lists and imposes no extra pointedness assumption. It gives rational linear forms, not just real separating forms. Deleting redundant inequalities terminates by strict decrease of a finite number. Step 3 uses only that defining equality and the spanning conclusion already obtained. The sum of nonnegative evaluations is zero only when every summand is zero. This proves strict positivity of x_0, and pointedness rules out an empty family in positive dimension.

Step 4 uses the meaning of irredundancy: the locus after deletion is strictly larger. The explicit coefficient alpha is rational, strictly between zero and one, and solves the desired zero equation. Thus every other inequality stays strictly positive. In step 5 the finite minimum includes 1, so it is defined even when no other functional changes along u. Each potentially negative displacement has magnitude at most half the positive margin. The displayed difference then puts every u in the span of F_i; no topological interior theorem is assumed. The definition statement cited in this step defines a facet by exactly that hyperplane-span condition. The same x_i excludes every other F_j, giving injectivity.

Step 6 again cites only that facet definition. The supporting form h is nonnegative on all generators; a zero sum of nonnegative terms eliminates every positive-valued generator. Therefore the zero-valued generators really generate F. This includes the empty list and the zero facet. Step 7 explicitly contradicts an assumed strictly positive list at their sum, using a rational v with h(v)=-1 and another finite positive minimum. It proves the existence of an active inequality without a separation theorem. In step 8 nonnegativity of its values on the zero-valued generators forces it to vanish on all of F. Containment and the two hyperplane dimensions give equality of kernels, and intersecting with the same sigma gives equality of facets. These are elementary finite-dimensional linear-algebra deductions, with every object introduced in the earlier steps.

Step 9 uses the finite lattice basis already supplied by step 1. A single positive integer clears all basis denominators, so the resulting map has integer values on every lattice element. Its image is nonzero because the lattice spans V and h_i is nonzero. Closure of that image under subtraction makes the integer-division remainder another image element; least positivity forces the remainder to vanish. This establishes surjectivity after division by b, rather than assuming a primitive form exists. Its scale N/b is positive, so the signs and the half-space equality are preserved.

Step 10 verifies uniqueness, not just proportionality up to sign. A second normal is nonzero by surjectivity; the span of the already established facet determines its hyperplane kernel. Taking g_0 of value one gives the displayed identity on every vector and an integer scalar c. The sum x_0 is in P and has strictly positive first-normal value, so nonnegativity and nonzeroness give c>0. Equality of the image with Z then forces c=1. Step 11 cites the lattice-intersection statement for precisely P=sigma intersect G. Multiplication by a positive denominator preserves every sign, and its formula checks positivity on each other facet, including all scale factors.

I tested the statement and constructions at P={0}, P=N and P=N^2, and on the nonsmooth saturated lattice cone generated by (1,0), (1,1), (1,2). The rank-one facet is {0} and its witness is allowed to be zero; demanding a nonzero witness there would be false, and is not done. In the last example the facet normals are y and 2x-y, both primitive on the full lattice. Duplicate or redundant input inequalities are removed before the construction; the arbitrary supporting facet argument still proves exhaustion. Changing an inequality by a positive rational factor changes none of the sign arguments, and division by the image generator removes all normalization ambiguity. Both explicit minima handle zero evaluations without division by zero.

I checked B--E in delivery-errors against these files: there are no new statement-only nodes to misstate, no duplicated tasks, no unlogged searches, no statement tags used instead of meanings, and no clause moved into a renamed lemma. All theorem uses are the statements of existing cited nodes, with literal quotations in citations.json; the remainder consists of the displayed elementary calculations. Both theorem dependencies belong to the same unit, so no off-route tool declaration is needed. The argument does not cite an ancestor depending on this item. No step exceeds 2000 characters (maximum 701), and the proof has 5704 characters in total. The 3000-character assembly restriction belongs to explicit re-split repair orders, and this item has none. Every original argument is retained, with the computations made more explicit.

## What remains unfinished

The intended stage-1 split is complete; Lean implementation remains outside this task. There are no new open mathematical tasks. The required server dry run and delivery are performed by the mandated delivery tool; their outcome is recorded in the final delivery line.

## Dry-run citation repair

The first delivery dry run rejected the short clause-(c) quotation in step 11 because it was under the gate's 40-character minimum. The statement did say exactly what the step uses; I replaced that quotation with the complete current lattice-intersection statement, rechecked it verbatim, and reran the dry run. The proof and all mathematical claims are unchanged.
