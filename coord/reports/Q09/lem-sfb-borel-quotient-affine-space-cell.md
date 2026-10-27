# Stage-1 report: lem-sfb-borel-quotient-affine-space-cell

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-borel-quotient-affine-space-cell.json: item, statement; split by reuse of an existing stronger theorem and two explicit elementary steps.
- citations.json: verbatim statement excerpts for every step/node pair.
- report.md and the search tool's searches.jsonl.

New nodes: 0. New Mathlib leaves: 0. No repository or launcher file was changed; no Lean was written or compiled.

## Attachments

None. The project-source search for the exact blueprint id and for Borel subgroup, borelQuotient, big cell and bigCell found no attachment in lean/WeilConjectures. The item's live node has no lean_audit or attached declaration.

## WANTED

None. All sources used are present.

## Findings and reuse

The imported statement is correct as written. I read Milne, Algebraic Groups, Lemma 18.21 and its proof (printed p.392), Proposition 13.52 (p.275), and the proof of Theorem 17.65 (p.374). The cell exists for general smooth connected affine groups; replacing this by a reductive-only Bruhat assertion without a reduction would leave a hypothesis gap. The existing lem-sfb-borel-quotient-affine-cell, created for the sibling effective-Picard-generators item, already states the same cell under identical hypotheses, and also regular integral Noetherian separated geometry. The duplicate rule therefore requires citing it, rather than creating another cell node or reproducing its future split.

I searched the whole DAG by source numbers 13.52/17.65/18.21 and cell/Borel terminology, and the imported blueprint using blueprint_refs.py searches for Borel, Borel quotient and affine-space cell. The whole DAG contains the stronger existing node; no blueprint node identified by these searches states this result. The reductive-only longest-cell and Bruhat-chart statements are not used. The new proof dependency has no outgoing proof dependencies and no path back to the item. The existing node remains an unsplit prerequisite; this delivery does not claim a finished Lean proof.

I read the chapter and unit records and the latest blueprint under literature/blueprint/latest, including sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof (3). This is a subordinate algebraic-group tool on the recorded alteration/moduli supporting branch, with no change to any unit or chapter route. The existing null blueprint ancestor and full provenance chain are retained, as printed by blueprint_refs.py ancestor.

## Not duplicates

No new nodes. The overlap with lem-sfb-borel-quotient-affine-cell is resolved by citing that existing, strictly stronger statement. I have not edited either existing sibling or any of its users.

## Review by Q09

I checked delivery-errors B through E against the sources and the actual statements. For step 1 I opened lem-sfb-borel-quotient-affine-cell and compared every hypothesis: algebraically closed base, smooth connected affine finite-type group, maximal smooth connected solvable Borel, and the same fppf quotient. Its final clause supplies exactly the dense open U, integer n, and polynomial-spectrum isomorphism used here. No regularity, properness, representation, or reductivity is silently inferred. This reuses a previously existing theorem, rather than moving the item into a new restatement.

For step 2 I opened def-sbc-affine-space: its affine-base clause explicitly identifies the defined relative affine space with Spec of the polynomial ring. I opened def-weil-open-immersion: it explicitly characterizes an open immersion as an isomorphism onto an open subscheme. Composing the chart inverse with U into Q therefore meets that definition directly. The image remains precisely U, so density is the same closure assertion already supplied in step 1. These are elementary identifications, not uncited comparison theorems.

Step 3 checks the requested degeneracy explicitly: for G=B every test-algebra coset set is singleton, so the quotient sheaf is terminal; the representing scheme is Spec F by the mutually inverse representing maps. The zero-variable clause of def-sbc-affine-space identifies A^0 with Spec F, and the open-immersion definition verifies the resulting isomorphism. All steps are below 2000 characters; no hidden long-step lemma was introduced.

Small cases checked: the trivial group, a torus, and a smooth connected unipotent group each have G=B and give d=0; for SL_2 and its triangular Borel, Q=P^1 has the expected dense A^1. Positive characteristic is allowed throughout, and no Levi subgroup or characteristic-zero assertion is used. The general group case is inherited from the existing node with no extra hypotheses. There are no new statements to test. citations.json contains a verbatim excerpt for each cited node in each step.

The fresh msearch calls include LeanFinder in two phrasings, Loogle, grep and LeanSearch, with their actual records appended to the preserved inherited searches. The hits are topological quotients, general affine opens, affine projection, and dominance, not a Borel subgroup quotient cell. No service was unavailable. No fictitious query or Mathlib match was recorded. There are no new node sources requiring Stacks tags; the theorem source here is Milne.

## Unfinished work

None within this one-level split. The pre-existing stronger theorem is still an ordinary DAG prerequisite for its own worker to split.
