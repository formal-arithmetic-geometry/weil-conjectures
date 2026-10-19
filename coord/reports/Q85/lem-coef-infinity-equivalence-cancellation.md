# Stage-1 report: lem-coef-infinity-equivalence-cancellation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-cancellation.json`: statement, now split in four steps. Mathlib verdict: no match for the quasicategorical statement. Zero new nodes, zero new Mathlib leaves.
- `citations.json`: seven entries, one for each step/node citation, checked as verbatim substrings of the current cited statements.
- `report.md`: this report. `searches.jsonl` was written by the authorized search command; all seven fresh queries are retained exactly in the item's appended search records.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` and `Comparator/` by blueprint id, Joyal, categorical equivalence, quasicategory and quasi-inverse found no project declaration of this result. The matches for quasi-inverses concern ordinary derived categories or topological invariance. The upstream name table has no item entry. Upstream master is reference material, not a finished-proof certificate.

## Wanted literature

WANTED: an archived copy of Lurie, Higher Topos Theory, Theorem 2.2.5.1 and Proposition 3.1.3.5 (proof opening, printed p.156), for lem-coef-infinity-equivalence-cancellation. I read those passages online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no copy was downloaded or written into the shared project. The proof is marked agent-written because HTT is not archived in literature/. The project-local Scholze Six-Functor Formalisms PDF, Lecture II, printed pp.14-15, was also read, especially the functor simplicial set and inverse-triangle conventions.

## What was wrong or changed

The imported statement is correct. No hypothesis or conclusion was changed. The node had no proof, and its source place described a subargument without a numbered source locator. I checked HTT's actual use: after constructing a left inverse up to coherent homotopy, the proof opening of Proposition 3.1.3.5 says that this inverse satisfies the fiberwise equivalence condition. The present split writes the supporting cancellation argument explicitly using the existing Joyal nodes. It does not re-prove the stronger relative inverse extension and does not cite that parent as a proof dependency.

The functor-calculus node is needed only for full faithfulness in the proof, so it was removed from stmt_deps and included in proof_deps. The generic cross-unit use of its mapping-space theorem is declared in split_report.tool_uses; the item's unit has no equivalent mapping-space consequence. Its cone and limit claims are not used. The three remaining statement dependencies fix all the notions and the equivalence convention already named by the statement.

The existing six inherited Mathlib-search records are preserved as inherited evidence, not represented as fresh Q85 searches. The actual new searches use valid quoted Loogle patterns and return ordinary-category cancellation (CategoryTheory.Functor.isEquivalence_of_comp_left/right, Equivalence.lean:695/689). I read Equivalence.lean:679-700: these require ordinary Category instances and say nothing about coherent equivalence edges or the right-pinched mapping spaces. The AlgebraicTopology grep hits are the abstract Joyal trick and an ordinary equivalence of augmented simplicial categories, also not matches. Two natural-language phrasings, two Loogle patterns, two focused greps and one LeanSearch were run and their actual summaries logged. No service was unavailable.

## Unfinished work

None in the one-level split. Existing supporting nodes remain the existing DAG's responsibility. No Lean was written or compiled, and no build, Lake command, live-project write, or direct git command was run.

## Not duplicates

No new nodes were created. Whole-blueprint searches for `equivalence cancellation` and `categorical equivalence` returned zero blueprint nodes. The existing Joyal model-structure and characterization nodes already provide the necessary non-elementary ingredients. The DAG search and direct statement inspection therefore led to reuse, rather than creating another cancellation or homotopy-invariance node.

## Review by Q85

I read the worker contract, stage-1 rules, SETUP's three levels, GOAL, dag-sync, delivery-errors B through E, the item's chapter and unit records, and the current blueprint ancestor's proof paragraph 2. The item is an auxiliary coherent-realization lemma, not its unit's key proposition, so no unit realized fields are changed. Its historical blueprint ancestor and from.place are retained, and same_as remains the empty result of the whole-blueprint search. The source route is Joyal quasicategories; no SGA source is used.

For step 1 I opened both def-cbc-enhanced-diagrams-cones and lem-coef-joyal-quasicategory-characterizations. The former defines functor equivalence by a quasi-inverse and two coherent comparisons; it does not demand an adjoint-equivalence triangle relation. The latter's clause (2) explicitly identifies precisely these data with Joyal weak/categorical equivalence. With u=rf, the proposed quasi-inverse is the actual identity simplicial map of X, and both composites are literally u. Thus the single given equivalence edge supplies both comparisons, without any missing homotopy-invariance lemma or a replacement of coherent equivalence by an arbitrary natural transformation. Both source and target are the hypothesized quasicategory X. This is an application of the cited theorem, so the step is not labelled elementary.

For step 2 I opened lem-coef-joyal-model-structure. Its statement explicitly identifies categorical equivalences with weak equivalences and asserts two-out-of-three. The composable maps really are X -> Y -> X, and the two known weak maps are f and rf. Cancellation therefore yields r with exactly the claimed convention; no model properness or lifting axiom is needed. This step is not labelled elementary.

For step 3 I rechecked clause (2) with source Y and target X: it produces s:X -> Y, sr equivalent to id_Y and rs equivalent to id_X, with the correct variances. I opened the current statement of lem-cbc-enhanced-functor-cone-calculus and used its literal sentence 'Every functor equivalence induces equivalences on all mapping spaces.' This is stronger than the mapping-space conclusion needed and uses the same mapping convention from def-cbc-enhanced-diagrams-cones, whose full-faithfulness definition I also checked. I did not try to derive that non-elementary mapping-space assertion from a definition. The generic cross-unit theorem use is explicitly declared for maintainer review.

For step 4 I checked the inverse-triangle definition in def-cbc-enhanced-diagrams-cones and Scholze's local printed p.14. Restriction to a vertex is a simplicial evaluation map. Applying it to the comparison rs -> id_X, its inverse, and the two triangles produces an actual equivalence r(s(x)) -> x. This is the entire elementary argument for essential surjectivity, written out rather than hidden behind 'transport'. It requires no choice of an object beyond the already supplied s(x). This step alone is elementary.

I checked small cases: if X is empty, the stipulated map r:Y -> X forces Y empty, so both mapping and object conclusions are vacuous. If X is terminal, a categorical equivalence f forces Y equivalent to it and the same argument applies. On nerves of ordinary categories the proof reduces to ordinary cancellation. The hypothesis on f cannot simply be omitted: inclusion of a point into a discrete two-point category has a retraction but that retraction is not fully faithful. No nonemptiness, connectedness, or extra hypothesis has entered the proof. X and Y can always be placed in one common allowed universe as in the original conventions.

For B1-B10, this delivery creates no unsplit statement, no new notion and no Mathlib leaf; all objects are introduced in the unchanged statement and TeX uses one decoded backslash. Every new search was actually run. For C1-C8, I inspected all four cited statements, extracted exact quotes, checked the hypotheses and the direction of each application, and declared the sole cross-unit tool use. A traversal of all statement and proof dependencies of each theorem used found no path back to this item (69, 76 and 143 nodes in the three respective closures), hence no introduced cycle. For D1-D5, all mathematical work remains in four explicit steps, with no new node restating a clause and no induction or omitted source argument. For E1-E7, the category, mapping-space, variance and homotopy conventions agree; no source or statement error was found. Each step is below 2000 characters (589, 369, 645 and 526), so no long-step lemma is hidden. The correction made during review was to replace a prospective generic 'homotopy invariance' invocation by the explicit identity-quasi-inverse construction in step 1, which needs no new node.
