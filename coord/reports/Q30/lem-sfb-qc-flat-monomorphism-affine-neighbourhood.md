# Stage-1 report: lem-sfb-qc-flat-monomorphism-affine-neighbourhood

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qc-flat-monomorphism-affine-neighbourhood.json: statement, split into three proof steps; Mathlib verdict no exact match. Statement and statement dependencies retained.
- citations.json: one verbatim statement quotation for each step/node citation.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes and no new Mathlib leaves. No unit realization update: this is a supporting lemma, not the unit's key statement.

## Attachments

None. Searched the project WeilConjectures source by the blueprint tag and the flat-monomorphism/affine-neighbourhood notions. No project declaration proves every clause without sorry. The existing project affine-cover criterion is generic and does not state this item.

## Literature wanted

WANTED: Raynaud, Un critère d'effectivité de descente, §1 Proposition 1.5(i), printed p.3, for lem-sfb-qc-flat-monomorphism-affine-neighbourhood (project path literature/raynaud-critere-effectivite-descente.pdf).

Read the primary Numdam scan online, https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf, including Proposition 1.2(i) and the proof of Proposition 1.5(i). No download made. The archival file is absent, so proof_origin is agent, with the argument and its source identified. Corrected the inherited source-place claim that a sandbox PDF had been read; it was read online.

## Problems and corrections

The imported item was statement-only; no statement dispute was found. Raynaud proves the stronger existence of a largest such open. The current existential statement faithfully retains the needed part and adds no hypotheses. The source chooses an affine target chart, lifts an affine source neighbourhood to an open in that chart using the ringed-image theorem, and applies the affine-source/separated-target criterion. I expanded why that open is separated and why the union has affine inverse images on an affine cover.

The current latest blueprint direct-images proof, clause (3), and its unit/chapter records were read. This supporting algebraic-geometry lemma follows the inherited affine-neighbourhood branch; it does not substitute another route for the direct-image theorem. The existing blueprint ancestry is a chain of generated support nodes with no imported ancestor returned by blueprint_refs. Retained its via list and made from.place explicit. Whole-blueprint and DAG searches found no blueprint statement identical to the item.

Searches from the initial node were retained and their returned declarations read. The additional leanfinder, loogle, grep and leansearch queries are recorded exactly from msearch.py. A second semantic phrasing was already logged in the inherited searches. FlatMono.lean:25–27 requires surjectivity for the isomorphism theorem; :38–39 requires local finite presentation for the open-immersion theorem. Neither specializes to this item. Two Loogle queries returned unknown-identifier diagnostics; recorded as inconclusive rather than evidence of absence. Semantic and source searches returned affine criteria, not the asserted open neighbourhood.

## Not duplicates

No new nodes. A draft affine-local-target candidate was discarded after locating pqf-lem-affine-local-target (Stacks 01S8), which states exactly the needed cover criterion. Reused it instead. Also searched the whole DAG for the relevant tags and affine/flat-monomorphism statements, and read the existing quasiaffine-neighbourhood lemma: it assumes quasi-affine source and quasi-separated target and does not replace this item. The existing ringed-image theorem supplies the embedding input, rather than being restated as a new lemma.

## Review by Q30

I checked delivery-errors B through E against the actual node and sources. The item has an argument rather than an application of a renamed clause; there are no new statement-only nodes, no changed target, no hollow construction, and no SGA source. I read all cited statements, not only their titles, and copied their verbatim statements into citations.json. The existing ringed-image node is now split and independently reviewed in the live repository; only its canonical locally ringed subspace identification is used here.

Step 1 uses lem-sfb-qc-flat-monomorphism-ringed-image with exactly its hypotheses: quasi-compact, flat, monomorphism, no finite-presentation or separation condition. Its explicit subspace topology makes an affine source chart V the trace E intersect W of an open W in an affine target chart A. The chart choices are part of the definition of scheme (def-pc-scheme), applied to open subschemes, not a compactness claim. Under the identification E with X, the notation E intersect W = V means the image of V, so f inverse image W = V. No assertion that f(X) is open is made.

Step 2 uses lem-weil-pbc-morphism-affine-schemes-affine for A to Spec Z; both schemes are affine. Clause (3) of lem-weil-pbc-affine-morphism-permanence then says that map is separated. I expanded the diagonal square: the inclusion W into A is monic from its actual open restriction (def-weil-open-immersion), hence W fibre product over A with W is W. This is the pullback of the absolute diagonal of A along W times W to A times A. The statement of lem-weil-pbc-closed-immersion-base-change has no finiteness assumptions and gives a closed diagonal for W. def-weil-proper-morphism defines separatedness by exactly this diagonal. Thus lem-weil-pbc-affine-source-separated-target-affine-morphism applies to V to W: V is affine and W is absolutely separated. Its conclusion, unpacked with pqf-def-affine-morphism, gives affine inverse images of every affine open B of W. This does not presume W affine or quasi-compact. The short diagonal argument is written out, not hidden behind a definition citation.

Step 3 constructs U as the union of the actual W. Each f(x) belongs to its corresponding W, so the image lies in U. Restricting the map and structure sheaf gives the factorization through the open subscheme (def-weil-open-immersion). Cover each W by affine charts (def-pc-scheme); step 2 gives affine inverse images. The exact statement of pqf-lem-affine-local-target says that one such affine covering suffices, so it proves X to U affine. This is a genuine cover of all U, including points outside f(X), rather than just a cover of the image. No quasi-separatedness, finite presentation, or quasi-affineness assumption appears.

I tested the empty-source case: U may be empty and the empty affine cover makes the same criterion apply. For the identity of an arbitrary scheme, including a non-affine or non-quasi-separated scheme, the conclusion is the affine identity with U=S; the proof only uses affine charts locally. For Spec A_p to Spec A the construction requires no finite presentation. A quasi-compact open immersion may have non-affine source, but taking the image as U gives the affine identity, consistent with this proof. These checks rule out the tempting incorrect strengthening that X itself must be affine. The topology trace, restriction factorization and monic diagonal arguments take only definitions and elementary universal properties; all non-elementary geometric inputs are cited existing nodes. All steps are shorter than 2000 characters.

## Unfinished work

None in the mathematical split. The archival source request remains WANTED. Server preflight and direct delivery follow this report.
