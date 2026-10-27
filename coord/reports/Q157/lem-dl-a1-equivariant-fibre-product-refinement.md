# Stage-1 report: lem-dl-a1-equivariant-fibre-product-refinement

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-equivariant-fibre-product-refinement.json: statement, split into eight steps; searched again with LeanFinder (two phrasings), Loogle, LeanSearch and the required grep command; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each cited node in each step.
- searches.jsonl: actual search-command records. No new nodes or Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and equivariant fibre/product/idempotent-refinement terminology. The existing group-action sheaves and henselian clopen/idempotent results do not state this item. The upstream localization-prime-residue-field theorem is used through its existing DAG node, not claimed as an attachment of this item.

## Wanted sources

None. All sources needed are present and read locally. No SGA source is used.

## Findings and changes

The item was unsplit; its statement is correct and unchanged. Its source, Stacks 0BST, explicitly asks the reader to supply the equivariant clopen refinement, suggesting idempotents. I wrote that construction instead of introducing a new node for the same assertion. In particular, a group need not permute the original product factors, and connectedness of those factors is never assumed. The coordinate units and the products of all their translates supply the refinement; integrality is used only for closedness of the image of the finite union of unwanted pieces. This needs no Noetherian or module-finiteness assumption.

The live node had searches from its creator, Q107. These are retained, and Q157's actual searches are appended. The two new LeanFinder phrasings returned orbit/Frobenius facts or profinite-space clopen partitions. The latter require Hausdorffness, unavailable for a general ring spectrum. LeanSearch's etale splitting theorem requires module finiteness and produces an etale change of base, rather than this principal-localization conclusion; its source header in RingTheory/Etale/QuasiFinite.lean was read. Thus these hits do not finish this item.

## Unfinished work

None in this stage-1 split. No Lean file was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes. Existing generic facts on clopen idempotents, integral closed maps, principal opens and localization residue fields are reused. The whole imported blueprint was searched for idempotents and for the equivariant-refinement statement; no blueprint node states this item in another form. The nearest ancestor is rem-dl-a1-conventions. The current main-20261015 conventions and the recorded setup unit/chapter were read; this split implements the existing finite-inertia route for the unramifiedness equivalence, rather than changing that route.

## Review by Q157

I read the entire third reduction paragraph of Stacks 0BST (pione.tex, lemma-inertia-invariants-etale), including its surrounding reductions, and compared it with the item. I also read algebra.tex at Tags 00EE (lemma-disjoint-decomposition), 00GU (lemma-integral-going-up), 00HZ (lemma-going-up-closed), 00E3 (lemma-spec-localization) and 00E4 (lemma-standard-open). These are the source assertions used by the existing nodes; there is no new node requiring a separate source review. I opened and read the actual statements of every cited DAG node before writing the steps and copied the statements verbatim into citations.json.

Step 1 uses def-weil-affine-spectrum only for the prime-ideal spectrum, not for a hidden decomposition theorem: the coordinate-unit calculation proves the product-prime classification directly. A prime contains all coordinate ideals except exactly one, so its contraction and uniqueness follow from the factor projections. Step 2 is the explicit finite product calculation: distinct functions have a coordinate giving a zero product, the finite sum expands to one, and the formula for h acting on indices follows by reindexing g to h inverse g. This is a routine algebra calculation, not an additional lemma node.

Step 3 uses exactly the converse clause of lem-weil-pbc-spec-clopen-idempotent, namely that D(e) is clopen for an idempotent. The finite partition and its fibre count are then established by primality and the sum-one equation, not assumed. Fixing B is checked explicitly to ensure that the group preserves the fibre and hence preserves the set J of retained indices.

Step 4 applies lem-weil-pbc-integral-spec-closed-map to the closed finite union Z: every element satisfying a monic polynomial supplies precisely its integrality hypothesis. It applies both clauses of lem-weil-pbc-spec-localization-away-basic-open: its basis clause chooses b outside p, and its localization clause describes the inverse image as D(phi(b)). Disjointness is proved by contracting an alleged common point. There is no appeal to finiteness of S as a B-module.

Step 5 uses the uniqueness assertion of lem-weil-pbc-spec-clopen-idempotent to conclude that a localized unwanted idempotent equals zero; empty support alone is not silently treated as zero for a general element. The full statement of lem-weil-pbc-localization-prime-residue-field-iso includes both directions of the prime correspondence and contraction/extension inverses. Applied to powers of b and phi(b), it guarantees all and only the original fibre primes survive. It is legitimate because b is outside p and each Q_i contracts to p. This generic off-unit tool is declared in split_report.tool_uses; the other off-unit lemmas are Mathlib leaves.

Step 6 writes both compositions of the proposed maps, using the orthogonality and sum-one equations already proved. It specifies that e_j is the unit of e_j S_b and gives the B_b scalar map, so the result is an algebra isomorphism, not just an additive bijection. Step 7 constructs the localized action on fractions and checks well-definedness against the explicit equality-of-fractions relation. It uses the same index action as step 2, and its inverse is h inverse, so the claimed permutation does not rest on a missing equivariance theorem.

Step 8 uses the residue-field clause of lem-weil-pbc-localization-prime-residue-field-iso for the two localization maps. The statement guarantees compatibility with the ring residues. I write the resulting fraction formulas and compare their images under h before and after localization, which proves equivariance including the maps between different prime residue fields. The quotient calculation for e_j S_b explains the relation to the factor residue fields. Compatible base residue-field isomorphisms preserve the defining power condition for pure inseparability, so no normality or separability hypothesis is inserted.

I tested the trivial group (the products reproduce the original idempotents), n=1 (the sole factor already works), an initially equivariant partition (no additional fibre pieces), empty refined members and nonzero refined members missing the fibre (both are removed after localization), nilpotents (handled by idempotent uniqueness, not reducedness), and arbitrary non-Noetherian integral extensions (the closed-map input still applies). The zero ring cannot satisfy the hypothesis that each factor has a prime above p; the fibre is nonempty because n is positive and each factor contributes one prime. No injectivity of B to S is used. Distinct retained indices remain distinct after localization because they have distinct surviving fibre primes. Every step has fewer than 2000 characters, and none hides a separate comparison lemma. Against delivery-errors B–E I checked statement self-containment, single TeX escaping, actual search logs, exact citation clauses and hypotheses, absence of cycles and of redundant or clause-restatement new nodes. No mathematical statement correction was necessary.

## Repair of the returned delivery (2026-10-23)

The return identifies branch head 66150d93809 and says its reader approved the split but landing refused the unpromoted side completion. I continued the saved returned node, report, citation file and five actual Q157 search-log entries. The initial required dry run passed at 67afee59d1e. The current read clone still marks this item unsplit, with no proof and no stage-1 repair note; its statement and statement dependencies agree exactly with the saved version. I rebased the worker-owned split fields onto that current node record; deliver.py constructs the delivery on freshly fetched origin/sheaf-dag and preserves maintainer metadata.

I re-read all five current cited statements, including the localization node's full three clauses, rather than relying on the earlier review. All seven citations.json quotations are still the complete verbatim current statements. The clopen-idempotent uniqueness and converse clauses, the integral closed-map hypothesis without module finiteness, both principal-open clauses, and both directions of the localization prime correspondence remain exactly the inputs needed in steps 3–5. No cited statement change requires a dependency replacement. Step 8's cited residue-field isomorphism uses local-ring quotients, whereas the item uses fraction fields; I added the explicit mutually inverse fraction formulas identifying these conventions.

This repair also expands step 5's commuting localization square to justify both directions of the fibre correspondence, and checks the group multiplication law on localized fractions in step 7. These strengthen the assembly argument without changing the statement, its hypotheses, the dependency set or the source route. I re-read Stacks 0BST's entire equivariant-refinement paragraph, the surrounding finite-inertia reductions, and the supporting algebra assertions at 00EE, 00GU, 00HZ, 00E3 and 00E4. The current main-20261015 conventions still require the same finite-inertia route. Each step remains under 2000 characters and no new lemma is hidden in these fraction calculations.

The existing search results are retained and re-read: the idempotent search is about invariant subspaces, the etale splitting hit assumes module finiteness and an etale base change, and the prime-orbit/profinite hits do not give this principal-localization refinement. The statement and search questions have not changed, so searches were not repeated. I rechecked the trivial group, one factor, empty refined pieces, nilpotents, and arbitrary integral maps without injectivity or Noetherianity. There are no new nodes or Mathlib leaves.
