# Worker report: lem-sf-ringed-open-total-tensor-kflat

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-ringed-open-total-tensor-kflat.json`: statement, split into five proof steps; no exact Mathlib match found.
- `citations.json`: fifteen entries, one for every step-node citation, each copied verbatim from the cited statement.
- `report.md`: this report and signed mathematical review.
- `searches.jsonl`: actual search-command log; `prepare.py`: sandbox-only script assembling the item and citation file.

New nodes: 0. New Mathlib leaves: 0. The original statement, statement dependencies, source and provenance are retained. No Lean, repository, launcher or unit file was written.

## Attachments

None. I searched the project source `lean/WeilConjectures/` both for the item's id and for K-flatness, extension, tensor and localized/ringed-site terminology. The localized module adjunction/exactness declarations cover an input, not this item's natural chain isomorphism and K-flat clauses. Pro-étale finite-coefficient results are not the general assertion for arbitrary small ringed sites. I found no project declaration giving every clause to attach.

## WANTED

None: all sources used here are available locally.

## What was wrong or missing

The item was an unsplit, agent-formulated chain-level refinement of Stacks 0E8I, with no proof. There was no earlier split or report in this sandbox. The sheaf tensor isomorphism is not itself a chain-level proof: one must account for the countable coproduct in every total degree, additivity and the signed second differential. The K-flatness definition tests an acyclic complex in the first tensor factor, whereas the displayed comparison puts P first. The explicit signed interchange in step 3 resolves this order issue. The statement needs no correction and no STATEMENT-DISPUTED claim is made.

The current blueprint snapshot places the ancestor definition at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/def-weil-integral-rational-qbar-compact-support.md`. I read it, together with the recorded DAG unit/chapter and the parent split `lem-sf-integral-compact-support-constructible`. This item supplies the representative argument used in that parent's step 2 for open extension before integral reduction. The inherited DAG chapter/unit and provenance are retained; no route is replaced and the item is not a unit key statement.

## Not duplicates

No new nodes are introduced. The existing sheaf-level node `lem-weil-pbc-ringed-slice-extension-tensor` does not state a total-complex isomorphism or K-flat preservation and is used as an input. The adjunction/exactness, general colimit and homology nodes are likewise reused. Whole-blueprint searches for K-flatness and extension/tensor, and DAG searches by those concepts and source tags, found no blueprint node stating all of this item's clauses in another form; `blueprint.same_as` remains empty.

## Mathlib searches

The six searches appended to the item were actually run through the required `msearch.py NN lem-sf-ringed-open-total-tensor-kflat` command and are recorded in `searches.jsonl`: two different LeanFinder phrasings, Loogle for sheaf modules and tensor, LeanSearch for the projection formula and K-flat preservation, grep for KFlat/kFlat/extensionByZero/lowerShriek under Algebra, and a follow-up grep for the returned `HasGoodTensor₁₂` concept in Algebra/Homology/Monoidal.lean. All services answered successfully. Hits concern ordinary flat modules, presheaf tensor structure, Tor, or the condition expressing good associativity of complex tensor. None gives extension by zero on an arbitrary ringed slice site, the displayed natural chain comparison, or its K-flat consequence. Original upstream search records were retained rather than rewritten as searches by NN.

## Review by NN

I read delivery-errors B through E in full and checked the proof against the statements of every node cited. There is no newly created node to hide a clause of the item or an elementary calculation. The five proof steps themselves carry the argument. There is also no statement-only sublemma with a concealed proof, no Mathlib leaf claim to justify, no added hypothesis, no new definition and no SGA source.

For the sheaf input I read Stacks `sites-modules.tex`, Tag 0E8I (`lemma-j-shriek-and-tensor`), including its tensor-Hom/adjunction proof, and the entire statement of `lem-weil-pbc-ringed-slice-extension-tensor`. The latter explicitly gives a sheaf isomorphism natural in both module variables for any commutative ring sheaf on a ringed site; it does not require a constant ring or an open subterminal object. I use exactly that statement, not one of its internal proof constructions. I also read the statements and source constructions for localized module restriction/extension in Tags 03DI/03DJ; the cited module adjunction/exactness node states exactness of BOTH functors and the required adjunction. Thus there is no underlying-abelian or constant-coefficient identification being silently assumed.

Step 1 applies that adjunction and the precise statement of `lem-weil-pbc-left-adjoint-preserves-colimits`. I read its Stacks source `categories.tex`, Tag 0038 (`lemma-adjoint-exact`). Its small-index hypothesis holds because the total-degree pairs form a countable discrete set. The existence of the direct sums is explicitly part of `def-pc-tensor-complex-sheaves`, whose statement I read and compared with `homology.tex`, Tag 012Z (`definition-associated-simple-complex`). I invert the canonical coproduct comparison, then sum the sheaf isomorphisms. This proves degreewise invertibility and the stated insertion formula without a new lemma.

Step 2 uses only the sheaf isomorphism's stated naturality, the exact functors' additivity, and the stated total differential. The two displayed equations separately treat the horizontal and vertical arrows; additivity preserves multiplication by (-1)^p. I check equality on the coproduct injections, which are also a coproduct after extension by step 1. The same check for the components of chain maps gives naturality in both complexes. In particular no arbitrary infinite sum of maps with a common target has been smuggled into the differential. This is an elementary summand calculation from the cited inputs.

Step 3 uses the explicit definition `def-pur-sheaf-tensor-product`, read against `sites-modules.tex` Section 03EK, and the same total-complex definition. The swap of ordinary pure tensors is well defined because the coefficient ring is commutative; its inverse is the reverse swap, and both commute with restrictions before sheafification. The formula (-1)^(ab) times that swap extends by the coproduct universal property. I checked both coefficients in the differential and the inverse formula. Thus tensor symmetry here is proved in the step, rather than assumed as an uncited non-elementary theorem or promoted to an unnecessary node. Negative degrees cause no change to the parity calculation.

Step 4 uses the exactness node, the full clause (c) of `lem-sp-exact-functor-preserves-homology`, and `def-pc-kflat-complex`. I read all those statements and `sites-cohomology.tex` Tag 06YN (`definition-K-flat`), together with `homology.tex` Tag 010N (`lemma-exact-functor`). Clause (c) gives the natural comparison with homology for any abelian categories; applying it degree by degree has no boundedness restriction. Restriction of an acyclic test complex is therefore acyclic. K-flatness applies with that restricted test complex first, after which step 3 changes the factor order, exact extension preserves acyclicity, steps 1–2 give the total-tensor isomorphism, and step 3 returns to the factor order demanded by the K-flat definition. No flatness of individual terms, enough-points hypothesis, convergence claim or exactness of an infinite product is used.

Step 5 uses the same exactness and natural homology comparison, now for a map, and the resolution clause of `def-pc-kflat-complex`. Functoriality sends every cohomology isomorphism of P -> H to an isomorphism after j_!, so the resulting map is a quasi-isomorphism; step 4 supplies K-flatness of its source. I also read `def-pc-quasi-iso-modules` and `def-pc-acyclic-complex-modules` to verify that these words mean precisely the cohomology-sheaf tests used here. These are not extra facts beyond the definition and comparison already cited in the steps.

Small-case checks: P=0 or C=0 gives zero complexes and the unique comparison; an empty localized topos or the zero coefficient sheaf likewise gives the zero comparison. Concentrating both complexes in degree zero recovers exactly the sheaf-level isomorphism. Degrees (1,1) force a minus sign in the interchange, and the displayed coefficient calculation verifies it; the same identities cover arbitrary negative degrees. Unbounded complexes still have only two differential arrows per source summand, and their degree index sets stay countable. These checks revealed no need to change the statement. I checked that no step exceeds 2000 characters (lengths 782, 983, 822, 895, 628) and that all fifteen citation quotes occur verbatim in the cited node's statement.

The only off-unit non-leaf tool declared in `split_report.tool_uses` is the generic sheaf tensor isomorphism `lem-weil-pbc-ringed-slice-extension-tensor`: this unit has no other general ringed-site tensor projection formula. The general colimit and homology tools are Mathlib leaves and the module adjunction/exactness input lies in the item's own unit. No cited node states only a definition where a preservation theorem is needed.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own statuses and proofs. The required server dry run and direct push are performed after this review; their results are recorded below once obtained.
