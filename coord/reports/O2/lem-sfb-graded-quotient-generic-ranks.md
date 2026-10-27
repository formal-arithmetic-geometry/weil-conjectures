## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-graded-quotient-generic-ranks.json — statement, split with seven proof steps; no exact Mathlib match for the whole statement.
- citations.json — one verbatim statement quotation for every proof-step citation.

New nodes: none. New Mathlib leaves: none.

Attachments: none. Searches of lean/WeilConjectures for the exact blueprint tag, graded quotients and generic ranks found no declaration asserting all clauses. Existing generic-freeness declarations concern the ungraded algebra-module input only. The existing DAG node lem-pur-noetherian-algebra-module-generic-freeness supplies that input and is reused.

WANTED: none.

The item statement is unchanged. Its proof was empty. The source names Tag 00NX clauses (3),(8); finite projectivity is clause (2), while clause (3) is the finite-free direct-summand criterion. The proof distinguishes them. No statement dispute was found. The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor confirms this. I preserve that maintainer metadata and identify the precise inherited proof place in split_report.blueprint.

Nothing remains unfinished in this split. The existing generic-freeness theorem and finite-projective rank leaf are dependencies, not new work delegated under another name.

## Searches and reuse

I read the item's recorded searches and their results: they found homogeneous localization, individual finite-presentation free localization and finite-projective rank results, not the entire statement. Fresh msearch.py queries (two leanfinder phrasings, leansearch, loogle and grep) confirmed this distinction and are recorded verbatim in the item and searches.jsonl. I read Mathlib/RingTheory/Localization/Free.lean:78-95: the free-localization theorem assumes finite presentation over the base, whereas N can have infinite rank over R. I read Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean around isLocallyConstant_rankAtStalk and the existing rank-node statement; the result is the rank ingredient already in the DAG, not the whole simultaneous assertion. The leanfinder hits concerning homogeneous localization address the degree-zero homogeneous localization, not the ordinary localization at a base scalar used here.

Whole-DAG searches by titles, statements and source tags 051R and 00NX found the existing algebra-module generic-freeness and finite-projective rank nodes. Blueprint searches for "graded quotient generic ranks", "generic freeness", "projective rank" and "graded module" found no equivalent blueprint statement (the projective-rank query returned chain supertrace, which is unrelated). No new node was created. The latest blueprint direct-images proof and the item's chapter/unit records were read; this remains an algebra prerequisite below the inherited direct-images route.

## Not duplicates

There are no new nodes. In particular, I reuse lem-pur-noetherian-algebra-module-generic-freeness rather than introducing another Tag 051R lemma, and lem-weil-pbc-finite-projective-rank-locally-constant rather than another Tag 00NX rank lemma.

## Review by O2

I read algebra.tex at lemma-generic-flatness-Noetherian (Tag 051R, starting line 28458) and lemma-finite-projective (Tag 00NX, starting line 19027), checked their tag-to-label mapping, and opened every cited node's statement. The proof is an agent-written graded adaptation of those results, explicitly recorded as such. There is no SGA input. I read the current latest blueprint direct-images proof (3); its compactification argument is not replaced. The inherited longer ancestry describes this Hilbert-function prerequisite below that route, and is retained.

Step 1 uses the actual definitions of Noetherian ring, finite-type algebra and finite module. It proves quotient Noetherianity by lifting an ideal and its generators, domainhood from primality, finite generation after base change from the same lists, and the grading by two mutually inverse balanced maps. No base-change preservation theorem is being silently taken from a definition node.

Step 2 cites the complete statement of lem-pur-noetherian-algebra-module-generic-freeness. It allows a finite module over a finite-type algebra, not just a finite module over the base, and explicitly allows an infinite basis. All four hypotheses hold for R,D,N by step 1. This is a generic algebra tool from another unit, declared in split_report.tool_uses, because this unit has no corresponding generic-freeness statement.

Step 3 cites localization's fraction construction, finite-generation's generating lists, and projectivity's stated direct-summand equivalence. The grading inclusion/projection remain a retraction on fractions. A finite list has finite union of basis supports even when F has an infinite basis; restricting the retraction to that finite free span proves the stronger finite-free direct-summand clause directly. The displayed decomposition proves the summand assertion. Projectivity then follows from exactly the equivalence in its definition node. Thus no new projective-retract lemma is hidden here, and no finite rank of N_a or graded basis is assumed.

Step 4 takes precisely finite-projective stalk freeness and local constancy from lem-weil-pbc-finite-projective-rank-locally-constant. Its statement supplies both, with no Noetherianity hypothesis on B. I wrote out the two maps comparing localized and unlocalized residue-field tensors, so equality with the fibre dimension does not rely on a stronger unstated version of that node.

Step 5 is the elementary generic-point argument: B is a nonzero domain, every basic neighbourhood of any prime contains (0), and a locally constant function therefore has its value at (0) everywhere. This avoids an uncited connectedness or irreducibility theorem. The value r(d) is a natural number since the localized stalk is finite free. The same a is fixed before d is chosen.

Step 6 cites only the spectrum and ring-localization definitions and performs the prime correspondence and field comparison explicitly. The condition a outside p/I guarantees every displayed denominator is nonzero; the kernel and surjectivity checks give the residue-field isomorphism. Step 7 cites module localization's fraction relations and gives mutually inverse balanced tensor maps. The A-actions agree through the field isomorphism of step 6; I acts by zero and a acts invertibly, exactly the conditions needed. Consequently the final fibre comparison is canonical, in all degrees, on one principal open.

I checked delivery-errors B--E against these files. No new node needs standalone hypotheses or searches; all recorded fresh searches actually ran. Every step citation has its full verbatim statement in citations.json. No step uses a cited proof or a construction absent from its statement. There are no new proof dependencies that could form the usual parent-child cycle: the parent graded-Hilbert-function node is not cited. The finite-support retraction and tensor/quotient calculations are elementary proof steps, not inflated new nodes. Every step is below 2000 characters; none hides a separately stated lemma.

Small cases checked: A=0 has no prime I, so the assertion is vacuous; for an actual prime I, R and R_a are nonzero. For M=0 the basis/support lists are empty and r is identically zero. For C=A and M finite, the argument specializes to ordinary generic freeness. For C=R[t], M=C, the whole localized module has infinite rank and each piece rank one, illustrating why the proof must allow an infinite basis. For M=R[t]/(ct) with c nonzero in a domain, inverting c gives zero positive-degree pieces and rank one in degree zero; if c becomes zero after the chosen prime quotient, all degrees instead have rank one. Applying generic freeness after, rather than before, each quotient handles both cases. Nonhomogeneous choices of basis do not affect the finite-support retractions. No unnecessary hypothesis, such as C generated in degree one, was added.
