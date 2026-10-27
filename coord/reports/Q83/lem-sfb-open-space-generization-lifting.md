# Q83: lem-sfb-open-space-generization-lifting

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-open-space-generization-lifting.json: statement, split using existing nodes; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each step/node citation.
- searches.jsonl: actual searches recorded by msearch.py.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched all lean/WeilConjectures for the blueprint tag and generizing/generalizing terminology. Existing uses of Flat.generalizingMap assume flatness and concern schemes; they do not state the present algebraic-space result. No complete project declaration states the item.

## Wanted literature

WANTED: literature/rydh-submersions-effective-descent.pdf, section 1 paragraph before Remark (1.3), Remark (1.8), Remark (2.5)(2), for lem-sfb-open-space-generization-lifting. The inherited source already marks the local PDF missing. I did not download it. The delivered proof_origin is agent: the proof is a compactness argument from the cited DAG statements and the local Stacks sources, not a claim to have read Rydh's absent PDF.

## Corrections and mathematical findings

The statement is unchanged. Stacks Tag 040F (morphisms.tex, lemma-open-generizing) was read in full; it proves the scheme case by affine localization and Tag 0407 (algebra.tex, lemma-open-going-down). I read that algebra proof too. A new node asserting the scheme case would leave the main algebraic-space passage to justify, and a new node repeating the algebraic-space result would not be a split. Instead the proof uses existing constructible-topology inputs to give that passage directly.

The original item has no proof and no lean_audit record. Its inherited Mathlib searches and blueprint provenance were retained. Searches by Q83 additionally tried LeanFinder in two phrasings, LeanSearch, Loogle and Mathlib grep; all services answered. The grep hits and UniversallyOpen.lean:110-140 were read: isOpenMap_of_generalizingMap is the opposite implication with a locally-finite-presentation hypothesis; Flat.generalizingMap has a flatness hypothesis absent here. Topological map-specialization lemmas only preserve an already supplied specialization. None is an exact match or a one-line specialization for algebraic spaces.

The chapter record and unit record were read, together with the latest blueprint unit _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This input serves the inherited alteration/moduli descent route and does not replace a step of the unit. The ancestor command reports None for this imported created-node chain; I preserved its null ancestor and recorded its existing concrete place and via chain. Blueprint searches for generization, generalization and open generizing found no duplicate statement (the one generalization hit, det-pe-wlocal-components, concerns w-local closed-point retractions).

## Not duplicates

No new nodes were created. Existing atlas, point, constructible-topology, quasi-compactness and spectral-space nodes are reused.

## Review by Q83

I checked the delivery-errors B--E requirements against the item and its cited statements. The split has four actual arguments, and none of its steps is longer than 2000 characters. There are no statement-only new nodes to audit, no new notions without definitions, and no transfer of the conclusion into a newly named premise. The non-elementary inputs are in uses and their union is exactly proof_deps. citations.json quotes each cited node's actual statement, rather than its proof or its title.

Step 1 uses lem-a1-space-affine-etale-cover for an affine chart with a point above x_0. Its statement explicitly gives a point-surjective presentation by affine components. lem-a1-space-point-open-calculus explicitly gives open and continuous point maps for representable etale morphisms. Composition is open because the image of an open set is the successive image under two open maps. lem-weil-pbc-affine-scheme-qcqs states both quasi-compactness and quasi-separatedness of an affine; lem-weil-pbc-qcqs-scheme-spectral states exactly the resulting spectrality. I read the local atlas construction (Stacks 03FX), topology statement and proof (03BX), and Properties 094L. This step never assumes a chart U -> Y is etale or that the image of U is all of Y.

Step 2 uses the field representative supplied by def-a1-algebraic-space-point-classes (Stacks 03BU, including the common-extension relation, read locally). def-weil-affine-spectrum explicitly states that Spec K has one point. The affine qcqs node applies to Spec K. The hypothesis Y quasi-separated is exactly what lem-sfb-space-qcqs-permanence requires to make Spec K -> Y quasi-compact; I read Stacks 073B(1)-(2). The statement of lem-sfb-space-quasicompact-constructible-closed applies to this map because both source and target are quasi-separated; its image of the whole closed patch space is the singleton {y_1}. The statement of lem-sfb-space-constructible-topology-comparison then gives patch continuity for h:U -> Y, and identifies the scheme patch topology with the affine quasi-compact-open topology. I also read the local inverse-image lemma 0ECW, which supports functoriality but is not silently substituted for the stronger cited node statement. Neither h nor f needs to be quasi-compact in this step: only the field representative does. I checked that neither constructible input's dependencies creates a cycle with this item.

Step 3 uses def-weil-spectral-space for the neighborhood basis of quasi-compact opens and def-weil-pbc-constructible-topology for their patch closedness. The hypothesis of lem-weil-pbc-spectral-constructible-topology-quasi-compact is supplied by step 1; its statement is compactness for arbitrary patch-open covers, not just covers of constructible subsets. I read Stacks 0901 and the preceding constructible-topology discussion. The finite-intersection argument is written out by applying that statement to complements of F and the neighborhoods. Finite intersections of neighborhoods need only be open and contain u_0; the proof does not assume any affine intersection is affine. The empty finite list is explicitly V=U, so nonemptiness follows without surjectivity. Membership in every basic neighborhood has the correct direction: u_1 generalizes u_0, hence its image specializes to x_0.

Step 4 uses just the continuity clause of lem-a1-space-point-open-calculus, and explicitly tests each neighborhood of x_0. It is elementary from that cited statement and the definition of closure. It proves both clauses f(x_1)=y_1 and x_0 in the closure of {x_1}.

I tested y_1=f(x_0), the identity, a non-surjective open immersion, an empty source, and maps from a field. The identity admits x_1=y_1; for an open immersion the open image contains every generalization of an image point; an empty source leaves no x_0 to choose. Constant maps from fields to non-open non-generic points are excluded by the open-map hypothesis, so they do not supply a counterexample. No finite-type, finite-presentation, flatness, or surjectivity hypothesis is used. The target and all definitions in its statement remain unchanged.

The off-unit generic tools are declared in split_report.tool_uses: affine etale presentations, point-map calculus, and spectral patch compactness. The other spectrality and affine qcqs inputs are Mathlib leaves; definition nodes only provide their notions. These tools support the unit's inherited descent argument.

## Unfinished work

None for stage 1. The proof inputs already exist as DAG nodes, including unsplit constructible-topology lemmas whose proofs remain separate items.
