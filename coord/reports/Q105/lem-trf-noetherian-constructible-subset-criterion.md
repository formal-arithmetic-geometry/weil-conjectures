# Stage-1 report: lem-trf-noetherian-constructible-subset-criterion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-noetherian-constructible-subset-criterion.json: existing statement, now split in five steps; no exact Mathlib match. The statement, statement dependencies, source and ancestry are retained.
- citations.json: twelve verbatim quotations, one for each step/node citation.
- report.md: this report.
- searches.jsonl: the search command's own records of five searches performed for this item.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed.

## Attachments

None. Searched the project Lean source by the item's blueprint tag/id and by constructibility, Noetherianity and irreducible-closed-subset terminology. Read WeilConjectures/Mathlib/Topology/Constructible.lean: `Topology.IsConstructible.exists_isOpen_inter_subset_or` proves the forward implication, assuming constructibility. The item requires the converse. `PrimeSpectrum.isConstructible_of_forall_exists_basicOpen` in WeilConjectures/RingTheory/RelativeComponentConstructible.lean:46 is an affine-spectrum induction criterion with a different hypothesis; applying it globally requires additional arguments. Neither is an exact attachment. No declaration for the exact item was found in the project or Comparator.

## WANTED

None. The source is available locally.

## Corrections and source audit

No statement dispute. The item exactly specializes Topology Tag 053Z (lemma-characterize-constructible-Noetherian), implication (2) to (1), to a scheme with a finite Noetherian affine cover. A relatively open nonempty subset disjoint from E witnesses that E intersect Z is not dense. Conversely, the complement in Z of the closure of a nondense intersection is a nonempty relatively open disjoint subset.

The imported item had no proof. Its existing Mathlib searches, creation metadata and blueprint ancestry are retained. The new proof makes the scheme-to-topology reduction explicit and implements the source's minimal-bad-closed-subset argument. Its badness predicate is ambient constructibility of E intersect C. Reducing a minimal counterexample to an irreducible closed subset uses a binary closed decomposition, directly from the irreducibility definition. These choices write out the elementary operations in the source's argument; the unit's route remains intact.

Read the chapter sec-trace-formula and unit sk-i-curve-zero, and the current main-20261015 blueprint ancestor lem-trf-local-term-locality. This criterion is a general topology input below its existing flattening/Noetherian-approximation ancestry, used for the irreducible-fibre-locus proof. It changes no trace or purity route. Whole-blueprint searches for “noetherian constructible subset criterion”, “constructibility criterion”, “irreducible closed” and “constructible” found no blueprint statement of this converse criterion; same_as remains empty. The whole-DAG scan by Tags 053Z and 01OZ, titles and statement keywords located the already existing minimal-condition, affine quasi-compactness and constructibility nodes used here.

Five actual Mathlib searches were run through msearch.py: LeanFinder with the statement, Loogle with `Topology.IsConstructible, IsIrreducible`, grep with constructibility/Noetherianity/irreducibility alternatives, LeanSearch with the criterion, and LeanFinder with a second finite-locally-closed-union phrasing. All services answered. Read the returned hits and Mathlib/Topology/Constructible.lean and AlgebraicGeometry/Noetherian.lean. Hits define constructibility or give finite irreducible decompositions, quasi-separatedness, or local-to-global constructibility; none directly gives this converse. The five appended search records reproduce their actual queries and logged result summaries. Earlier searches belong to the imported node and were preserved.

## Unfinished work

None at the requested one-level split. No new unproved lemma is introduced.

## Not duplicates

No new node is created. Existing nodes supply every input.

## Review by Q105

I read Stacks topology.tex, Tag 053Z, including its entire converse proof, Tag 005L (lemma-constructible-Noetherian-space), and Definition 0051 (definition-noetherian). For the scheme reduction I read properties.tex, Definition 01OV and Lemma 01OZ, and algebra.tex, Lemma 00E8 (lemma-quasi-compact). I also opened and read the statement of every cited node. There is no new node whose independent source would need review.

Step 1 uses def-weil-affine-spectrum for the actual section ring of each chart, pqf-def-locnoeth for the affine-cover definition, lem-weil-pbc-affine-scheme-qcqs for quasi-compactness of each affine, and def-weil-pbc-quasi-compact-scheme to write the finite-subcover argument. This verifies both hypotheses of lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. That lemma states the required minimal condition for arbitrary nonempty families of closed subsets. I explicitly derive stabilization of descending closed chains, so the Noetherian-space hypothesis in Tag 005L is justified. The zero-chart empty scheme is allowed: the empty subcover covers it.

Step 2 cites that same minimal-condition statement for the nonempty family of ambient bad closed subsets. Nonemptiness follows only under the stated contradiction hypothesis. It uses the finite-union definition in def-weil-constructible-subset to include the empty union and hence exclude the empty minimal counterexample. Minimality proves constructibility of E intersect every proper ambient closed subset of C; this is the full induction hypothesis used later.

Step 3 uses precisely the irreducibility definition in def-weil-irreducible-components. If the nonempty C is reducible, both pieces are proper relatively closed subsets. The formulas C_i = C intersect F_i prove that they are ambient closed. Step 2 and the finite-union closure explicitly stated by def-weil-constructible-subset give the contradiction. This is an elementary application of the definition; no irreducible-component decomposition theorem is assumed.

Step 4 applies the item's hypothesis only after Step 3 has proved that C is nonempty, closed and irreducible. It exhibits V = C intersect O and D = C intersect (X minus O), verifies closedness and strictness of D, and invokes the induction hypothesis. def-weil-locally-closed-subset gives exactly the displayed locally closed presentation of V. def-weil-constructible-subset explicitly includes the finite-locally-closed-union characterization on Noetherian spaces, so its statement, not an unstated result from its proof, supplies constructibility of V. The relevant exact sentences are in citations.json.

Step 5 writes the equality for each alternative and uses only finite-union closure already stated in def-weil-constructible-subset. This contradicts membership in the bad family and proves the original conclusion. I checked both V contained in E and V disjoint from E, including V = C, E empty, E = X, an empty scheme, a one-point spectrum, and reducible finite discrete spaces. The nonempty-open hypothesis is essential to strictness; it is not silently replaced by density.

Against delivery-errors B–E, no statement-only child, duplicate, relabelled clause, uncited non-elementary sublemma, object change, extra hypothesis or circular dependency is present. All reductions marked elementary are written as the explicit set identities or definition applications they require. Every step has fewer than 2000 characters. All twelve quotations were verified as literal substrings of the actual cited statements. I corrected the first citation to quote the full locally-Noetherian cover criterion, and added the affine-spectrum section-ring citation explicitly. The report and split are my Q105 self-review; the maintainer provides the independent review.
