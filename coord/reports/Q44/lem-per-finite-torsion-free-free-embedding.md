# Worker report: lem-per-finite-torsion-free-free-embedding

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-torsion-free-free-embedding.json: statement, split; full theorem not a Mathlib match after fresh prescribed searches. Five steps, no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement excerpt for every proof-step citation.
- report.md and searches.jsonl: report and actual search log. write_split.py is sandbox-only preparation, not a delivered DAG file.

## Attachments

None. Searched lean/WeilConjectures/ for the exact item id/docstring tag, torsion-free terminology, finite-free embedding terminology, and read the resulting relevant contexts. No declaration states this result over an arbitrary domain. The PID freeness results used elsewhere add a hypothesis absent here.

## WANTED

None.

## Corrections and provenance

The live item was unsplit, and the sandbox contained no earlier item/report/search log. There is no repair note. Copied the item and retained its statement, statement dependency, inherited searches and created/blueprint provenance. Filled its proof, proof dependencies, proof origin and split report. Its inherited same_as was checked against whole-blueprint searches for torsion-free and fraction-field language: no exact counterpart. The ancestor is lem-per-artin-gabber-affine-curve, whose latest proof Step 3 concerns the duality direction, not this elementary commutative algebra result. This delivery continues the already recorded historical regular-pair refinement chain; it does not replace a unit step or assert that the latest blueprint directly states this lemma. The unit is not keyed by this item, so its realized fields were not changed.

The source is Stacks Tag 0AUU, more-algebra-lemma-finite-torsion-free-submodule-free (more-algebra.tex:4863-4881); its statement is an equivalence, of which this item requests the torsion-free-to-embedding direction. No statement dispute. Used the concrete localization S^{-1}M rather than tensor notation for the same fraction-field coordinate argument, avoiding an unnecessary tensor/localization comparison lemma. In particular, the common denominator product and the resulting R-valued coordinate map are written out instead of merely saying "clear denominators".

## Existing-node and Mathlib searches

Read all hits from the prescribed msearch.py calls recorded in searches.jsonl. Both semantic phrasings for the full embedding theorem return PID freeness/basis statements or rank/finiteness statements with a different conclusion. Read Mathlib/LinearAlgebra/FreeModule/PID.lean:103,139,329-404; IsPrincipalIdealRing is essential there and cannot be inferred for an arbitrary domain. The field-vector-space query and localization grep were ingredient searches. They lead to existing DAG nodes, not to a match for the full item. The historical NW searches remain in the item; fresh Q44 searches are appended, with their actual output digest summaries and conclusions.

Whole-DAG searches by 0AUU, its label, fraction-field, torsion-free/localization, and vector-space/basis terminology found the current item and its parent for the source theorem. Opened def-weil-pbc-module-localization, lem-weil-pbc-vector-space-free, def-weil-pbc-free-module and def-weil-finitely-generated-module and used them. Also inspected lem-sfb-scalar-finite-free-resolutions (finitely presented hypothesis), lem-trf-equal-dimension-linear-equivalence (requires an equality of dimensions), and lem-weil-pbc-localization-module-tensor (only principal localizations); none was used outside its actual statement. No new nodes were needed.

## Not duplicates

No new nodes. No new/existing same-tag pairs to distinguish.

## Review by Q44

I read the statement and proof of 0AUU in more-algebra.tex:4863-4881, the preceding torsion/localization discussion at 4794-4805, the module-localization construction in algebra.tex:1138-1168 (Tag 07JZ, algebra-definition-localization-module), and Fields Tag 09FN, fields-lemma-vector-space-is-free, fields.tex:155-165. Confirmed 0AUU's label in tags/tags. The item assumes exactly a commutative integral domain, finite generation and torsion freeness; neither the source nor the argument needs Noetherianity, normality, a PID hypothesis or a nonzero module.

Step 1 uses the statement of def-weil-pbc-module-localization for fraction classes and their operations, with M=R for K and with the given M for V. The fraction equality criterion is explicitly part of that statement. S is multiplicative because a product of nonzero elements in a domain is nonzero. Cancellation shows R injects in K, and the displayed inverse s/a verifies the field assertion directly; no fraction-field existence theorem or flatness result is being assumed silently.

Step 2 uses that same node's exact assertion "m/1=0 if and only if um=0 for some u in S". Because every such u is nonzero, the item's torsion-free hypothesis applies. def-weil-finitely-generated-module gives exactly the finite generator list used. The formula m/s = sum (c_i/s)j(x_i) proves finite spanning over K directly from the fraction operations; there is no invocation of a tensor-exactness or scalar-extension-finiteness theorem.

Step 3 uses lem-weil-pbc-vector-space-free, whose statement says every module over a field has a basis, and only that assertion. Its field hypothesis was checked in Step 1. def-weil-pbc-free-module gives finite-support unique expansions. The union of the supports of the finitely many spanning vectors is finite; if an index lay outside it, the corresponding basis vector would have conflicting coefficients 1 and 0. This explicitly proves the finiteness needed for the coordinate isomorphism, rather than taking a finite-basis theorem from an unstated stronger version of the cited leaf. The step is marked non-elementary because it invokes basis existence, although its subsequent finite-support argument is elementary. Both cited statements were opened, not their proofs alone.

Step 4 uses the previously constructed coordinates and the definition of fractions. Every denominator is nonzero and only finitely many occur, so their product is nonzero in the domain. The explicit omitted-factor product is an element of R and equals b times the indicated fraction. For an arbitrary element, the displayed sum over its generators proves that all multiplied coordinates are in R. Independence from the generator expression is proved using R's already established injection in K. This is an elementary calculation, not a new denominator-clearing lemma.

Step 5 defines the map by the unique R-preimages of the multiplied coordinates. Its linearity follows by comparing coordinates after the injective inclusion into K. A zero image gives b theta(j(m))=0; b is a nonzero scalar in a field, so theta(j(m))=0, then m=0 by the two injections. No projectivity, freeness of M or finite presentation is used. Steps 4 and 5 use only objects and facts proved in earlier steps, so their uses lists are empty and they are marked elementary.

Small cases checked: M=0 and an empty generating list (all products empty, b=1 and rank zero works); R a field (denominators can all be 1); a nonprincipal finite ideal such as (x,y) in k[x,y] (it embeds but need not be free, so the PID search hits are insufficient); and a torsion module Z/2 over Z (the localization map is not injective, locating the exact use of torsion freeness). A nonzero module with rank zero cannot occur: the injective j into the zero localized space forces M=0. All five steps are under 2000 characters, and their combined argument is under 3000 characters. No circular citation or hidden sublemma remains; all dependencies used are pre-existing Mathlib leaves/definitions, so no off-route generic-tool declaration is needed. No SGA source is used.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files: there are no new statement-only-node obligations, the item is a proof rather than a restatement in a child, every non-elementary external assertion is a cited statement, all citation quotes in citations.json are verbatim substrings, and each hypothesis is accounted for above. No correction to the source or the statement was required.

## Unfinished work

None in the requested stage-1 split. Server dry-run and push results are reported by the delivery command.
