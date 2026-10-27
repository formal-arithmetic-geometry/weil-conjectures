# Stage 1 report: lem-trf-section-proj-etale-embedding

## Files written

- dag/nodes/sec-trace-formula/lem-trf-section-proj-etale-embedding.json: statement, split; five proof steps using existing nodes, no new nodes, no new Mathlib leaves.
- citations.json: nine step/node entries, each quoting the cited statement verbatim.
- report.md: this report. searches.jsonl retains the actual search-command log.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for section algebra, canonical Proj, and etale section terminology, and read the relative-Proj source locations. No project declaration states the whole assertion for algebraic spaces. The affine Proj constructions found in Mathlib do not provide an attachment.

## WANTED

None. All sources needed for this assembly are present.

## Corrections and source comparison

The item had no proof. Its statement is retained verbatim, as are its statement dependencies, source, imported provenance and other maintained fields. The new proof makes the precise cover of the target explicit: it is the family P times_T T_i over P, rather than the family T_i over T. This distinction is necessary to apply open-immersion locality.

I read the current blueprint at literature/blueprint/latest (snapshot main-20261023-1620 in COMMITS.txt), including the local-term-locality proof and the unit. Its local-term proof now discusses contracting correspondences, not the older polarized-descent sentence named by this item's ancestry. The historical provenance is retained; the item's direct mathematical source is the section-algebra paragraph of Stacks Tag 0D3C, lemma-descending-property-ample in spaces-descent.tex, lines 2125 onward. Its proof constructs the section algebra, compares evaluations, proves the generation locus is all of X and descends the canonical open immersion. The present item assumes the local generation and immersion conclusions that the Stacks proof obtains from local ampleness. No route is replaced and no ampleness hypothesis is needed here.

Mathlib searches were run through msearch.py only, with two distinct LeanFinder formulations, Loogle, LeanSearch and grep. Each query is recorded exactly. The hits are affine Proj, scheme gluing, and open-immersion charts. I read Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, including awayι around line 185 and fromOfGlobalSections at line 443. The latter takes a graded ring and a ring map into global sections of an already given scheme; it does not establish the relative graded section-algebra and etale comparison assertions, nor representability of an algebraic-space source. The item is therefore not a Mathlib leaf. Existing historical search records were retained.

## Not duplicates

No new nodes were created. Existing lem-trf-space-section-algebra-etale-base-change, lem-trf-space-line-module-proj-map, lem-trf-space-fibre-products-etale-covers and lem-trf-space-open-immersion-etale-local were reused, together with the two more precise graded evaluation/restriction nodes and relative-Proj existence. Whole-DAG keyword/tag searches and blueprint_refs.py searches for section algebra, canonical map, Proj and open immersion found tools or partial assertions, not a second blueprint statement of this item. In particular local ampleness descent is stronger in its assumptions and has a different conclusion; it is not used circularly as a tool.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own downstream work. No Lean was written, compiled or built.

## Review by ND

I read Stacks spaces-descent.tex Tag 0D3C (lemma-descending-property-ample) in full, the definition and parts (2),(3) of spaces-divisors.tex Tag 0D2Z (lemma-invertible-map-into-relative-proj), spaces-properties.tex Tag 03LX (lemma-pushforward-etale-base-change-modules) including the tensor-pullback footnote, spaces-morphisms.tex Tag 03M4 (lemma-closed-immersion-local), and spaces-descent.tex Tag 041X (lemma-descending-property-open-immersion). I also read the latest blueprint's relative-Proj existence and arbitrary-base-change statements and the existence proof. There are no new nodes needing separate sources.

Step 1 uses the actual statement of lem-trf-space-section-algebra-etale-base-change for quasi-coherence and graded base-change/evaluation compatibility. Its assumptions are exactly the item's quasi-compact separated f, scheme base T and line module L. The statement of lem-trf-graded-evaluation-zariski-etale-comparison includes the tensor-power specialization and the assertion that the summed evaluation is a commutative unital graded algebra map; this is what validates the input to the canonical Proj construction. It does not merely define evaluation.

Step 2 uses lem-trf-graded-pushforward-etale-restriction. Its statement explicitly identifies the same compatible sections after etale base change and gives the local tensor formula a tensor s maps to a times s restricted to W. Its tensor-power clause includes degree zero and the actual restricted line module. Thus the normalization clause in the item is covered, including local scalar coefficients; it is not inferred from an arbitrary isomorphism of graded objects. There is no need to identify sections of an infinite coproduct with a direct sum on every open.

Step 3 uses lemma-nagata-relative-proj-exists, whose statement actually asserts a scheme exists, not just its defining chart data. This is declared as a generic tool in split_report.tool_uses because it is from the Nagata unit. The statement of lem-trf-space-line-module-proj-map provides an open generation subspace, its canonical morphism, the equality of generation loci on the scheme tests X_i and T_i, and the Proj base-change identification. These tests are schemes by the item's hypotheses, and the evaluation comparisons from Steps 1 and 2 identify its pulled-back input with the given psi_i. The use is cartesian; the source's wording about general commutative diagrams does not require a stronger noncartesian assertion here.

Step 4 uses lem-trf-space-fibre-products-etale-covers twice, once over X and once over P. Its statement gives both joint surjectivity after any base change and the scheme property of P times_T T_i (P is a scheme and T_i to T is etale). If x is a point of X, choose x_i over it; the generation-locus equality from Step 3 and U(psi_i)=X_i put x in U(psi). An open subspace with the whole underlying set is the whole open subspace X; this is only the interpretation of the open generation locus, not a new descent lemma. Associating the fibre products identifies X times_P (P times_T T_i) with X_i, and Step 3 identifies the resulting morphism with r_i. The statement of lem-trf-space-open-immersion-etale-local says precisely that a morphism tested on this jointly surjective etale scheme cover is a representable open immersion, and that a source mapping this way to a scheme is itself a scheme. No separatedness or quasi-compactness of P or of the family is silently used.

Step 5 uses the identity-base-change scheme clause of lem-trf-space-section-algebra-etale-base-change for the final ordinary Zariski algebra and evaluation comparison. It applies because Step 4 has now shown X is a scheme; the original quasi-compactness and separatedness still hold. The scheme clause of lem-trf-space-line-module-proj-map identifies the ordinary canonical map itself, rather than just its image. These two statements give every final comparison clause.

Against delivery-errors B, all used notions already have statement dependencies, the item introduces its own objects, the TeX is singly encoded, and sources identify both tags and labels. There are no new statement-only, duplicate or unsearched nodes. Against C, every step cites the actual theorem statement it uses, all nine citations are copied verbatim, and proof_deps is the union of uses. A tag does not substitute for a node. Against D, none of the conclusion was moved to a new node: the generation-locus argument and target-cover assembly are written in the item's steps. Against E, I checked the cover really covers P, scheme tests have scheme sources, evaluations use tensor pullback, and no extra finiteness/noetherian/positive-degree-generation assumptions are introduced.

For small cases, an empty X has empty generation locus equal to X and the empty open immersion. If T is empty the assertion reduces to this case. An empty indexing family can cover T only when T is empty, so the point-lifting argument is vacuous as needed. The one-element identity cover gives the already assumed canonical open immersion. No uniform degree over the family is needed: U is a union of all positive-degree surjectivity loci. Nothing assumes A_0=O_T. All proof steps have fewer than 600 characters; none hides a long inline lemma. No statement dispute or source correction was required.
