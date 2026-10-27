# Stage-1 report: lem-trf-filtration-successor-maps-independent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-filtration-successor-maps-independent.json — existing statement, split into five elementary steps; no exact or one-line Mathlib match.
- citations.json — the sole cited-node/step pair with a verbatim statement quote.
- report.md — this report. The six new msearch.py results remain in searches.jsonl.

New nodes: 0. Mathlib leaves created: 0. The existing direct-sum definition remains the only statement and proof dependency.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, successor/filtration phrases, transfinite direct sums, dévissage and maximal-support independence found no project declaration stating the item. Related spectral-sequence filtration declarations and triangular field independence results do not state this module theorem.

## WANTED

None. The source needed here is archived locally.

## Corrections and source alignment

The statement is unchanged. The item was unsplit and had no proof; the sandbox contained only brief markers before this attempt. There is no item repair note. All inherited searches, source, creation history and blueprint ancestry were retained.

I read Stacks algebra.tex, Tag 058V, lemma-direct-sum-devissage, especially its injectivity paragraph at lines 20435–20453. That paragraph separates the last summand from preceding summands and uses the direct-summand property. Here its precise necessary input is the given implication t_alpha(a) in X_alpha implies a=0. The maximal finite-support formulation proves injectivity without the source's generation, continuity, initial-zero or exhaustion assumptions; these are correctly absent in this child's statement. The argument is marked agent-written because it reorganizes the source's transfinite induction into a finite-support contradiction rather than claiming a verbatim source proof.

I read the chapter and unit records and the latest blueprint sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md (latest points to main-20261023-1620). The current ancestor uses contracting correspondences and no longer contains the old imported algebraic ancestry. This item is the already-created algebra helper in that inherited ancestry: this split changes no chapter/unit route and makes no claim about local terms. Its blueprint.from place remains the explicit 058V injectivity clause, and same_as is empty. blueprint_refs.py ancestor returned lem-trf-local-term-locality; whole-blueprint searches for 'filtration successor', '058V', and 'independent modulo' returned zero matches.

## Mathlib searches and verdict

The item retains its creator's five recorded searches and adds all six searches actually run by Q77 through msearch.py; their exact query strings and returned digest summaries are recorded in the node and searches.jsonl. I tried both the sum-map and predecessor-independence phrasings. All four services/kinds used were available.

I read Mathlib/LinearAlgebra/DFinsupp.lean:480–565 and 590–610. iSupIndep.dfinsupp_lsum_injective requires independence from the sum of all other submodules; the finite-sum characterization expresses that same stronger input and does not derive it from the one-sided hypothesis. Mathlib/Algebra/DirectSum/Module.lean:270 concerns a componentwise map between two direct sums. The maps in the item have a common ambient target and may cancel there, which is precisely the issue to prove. The other Loogle hits concern one summand, direct-sum maps, or injectivity of the map constructor. Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean:323–332 shows injective_sum_to is a set-theoretic disjoint-union map for good/max products, not a direct-sum module map. The Hahn strata hits require an Archimedean ordered division ring and ordered module. None is an attachment or a one-line Mathlib leaf.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The existing split-transfinite-module-filtration parent is a stronger decomposition theorem whose proof already depends on this child; citing it would be circular. The sibling transfinite-successor-generators-surjective proves generation, not injectivity. Whole-DAG tag and concept searches were used to check that this short argument did not need another task.

## Review by Q77

I checked delivery-errors B–E against the node and source. There is no new statement-only node, no moved clause, no source cited in place of a proof, and no hidden non-elementary lemma. Every step is under 400 characters; none exceeds the 2000-character review threshold.

Step 1 cites def-weil-pbc-direct-sum-modules, whose complete statement I opened. It explicitly defines elements as finitely supported families, componentwise operations, inclusions, and decomposition into a finite sum. That is exactly what this step uses. The step writes out linearity on the finite union of supports, so no unrecorded universal-property theorem is used. citations.json quotes its finite-sum formula verbatim.

Step 2 uses only the element's finite support and the linear order on ordinals. The proof supplies the singleton/adjoin induction producing a maximum; it does not cite an unproved selection lemma. The empty support case is explicit. In Step 3, alpha != gamma together with maximality gives alpha < gamma and thus alpha+1 <= gamma, not merely alpha <= gamma; both indices lie in the given filtration's range because gamma < kappa. Monotonicity puts every earlier image in X_gamma. Closure of a submodule under finite addition is explained by finite induction and negation is part of its definition. No continuity or surjectivity is being smuggled into this step.

Step 4 writes the equation isolating the last term and applies the item's actual hypothesis at gamma and a_gamma. The ambient equation takes place in X with the included value of t_gamma; membership in X_gamma has exactly the meaning in the hypothesis. The contradiction uses a_gamma != 0 from the definition of support. Step 5 applies the already proved zero-preimage assertion to a-b and uses componentwise subtraction, explicitly reducing ordinary injectivity to that assertion. Steps 2–5 cite no external node because their small order, group and submodule arguments are supplied in full.

I tested kappa=0 (empty family, zero domain), kappa=1 (the hypothesis directly makes t_0 injective), arbitrary limit kappa (a finite support still has a largest element), zero ring/modules, and a plateau X_alpha=X_(alpha+1) (the hypothesis then forces A_alpha=0). A nonzero X_0 and a nonexhaustive terminal stage do not affect the argument. Without the successor implication, taking two equal nonzero maps into a constant filtration would give cancellation; the proof correctly uses the implication exactly where needed. No statement correction or dispute is required.

I checked that proof_deps equals the union of uses, that all statement dependencies are still needed, that the only quotation is a literal substring of the cited statement, and that no new cycle can arise from adding the existing definition leaf. No off-unit theorem tool, prohibited SGA source, Lean writing or compilation is involved.

## Unfinished work

None in this split. Delivery validation and push results are recorded below after they complete.

## Delivery validation

The required deliver.py --no-push invocation exited successfully: OK (not pushed) at efccbbb23e7, server preflight passed. The final push reruns the same checks on this report addition.
