## Worker report

Q05, stage 1, 2026-10-23. Item: lem-sfb-noetherian-generically-constant-finite-image.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-generically-constant-finite-image.json: statement unchanged; four-step proof, proof dependency union, agent proof origin, new search records, split report, status split.
- citations.json: one verbatim statement extract for each step/node citation (three entries).
- report.md: this report. searches.jsonl contains the actual msearch.py records.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. Reuse lem-weil-pbc-noetherian-finite-module-acc, an existing Mathlib leaf, instead of introducing a second maximality or Noetherian-induction node. The two-principal-ideal argument and the principal-open complement argument are elementary steps, not new nodes restating parts of the item.

### Attachments

None. I searched lean/WeilConjectures by the exact blueprint tag and by generically.constant, finite_range, finiteRange, finite_image, and the relevant RingTheory/Spectrum directories. The finite-image declarations found concern other hypotheses (smooth cochains, Weil characters, finite morphisms), not this arbitrary set-valued map. GenericFlatness.lean uses finite_range only for finite generators. No complete project declaration states this item. No Lean was written and no compiler or Lake command was run.

### WANTED

None. The cited Stacks sources are present. This is explicitly an agent-written finite-image adaptation of a Noetherian-induction pattern, not a claim that Stacks 0ASY states this lemma.

### Findings and changes

The live item was unsplit with no proof. No previous sandbox node, report or search log existed, and there is no repair note for this item. Its statement is true without continuity and without a nonzero-ring assumption; I did not change it or its statement dependencies, source, created record, chapter/unit, or inherited blueprint ancestry.

The source mentions 00FR (finite minimal primes), but the split does not need that theorem: a maximal bad ideal is itself prime. If a proper maximal bad ideal I were not prime, choose a,c outside I with ac in I. Then V(I) is exactly V(I+(a)) union V(I+(c)), contradicting maximality. This replaces the longer minimal-prime decomposition within this node, below the fixed unit route; no keep_plan repair order applies. The sole non-elementary input is already a Mathlib leaf.

All parts are finished for stage 1; the required server checks and delivery are performed after this report is written.

## Blueprint and duplicate searches

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json, together with the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md (front matter det-thm-sf-ctf-stability-direct-images), especially (3). This is a lower-level Hilbert-construction prerequisite along the existing alteration branch; it does not alter the chapter or unit statement. The inherited chapter/unit naming mismatch in those records is not edited by this delivery.

blueprint_refs.py ancestor reports None, as it already does for the reviewed parent; retain the complete existing from.place and via chain. blueprint_refs.py searches for 'Noetherian induction', 'finite image' and 'generically constant' find no equivalent blueprint result (the finite-image hits are rank-one degree data). Whole-DAG searches for 00IK, 00FR, 0ASY, ascending chain, maximal element, Noetherian induction and well-foundedness found the existing finite-module maximality leaf. Read its whole statement before using it. The nearby finite-minimal-prime and generic-flatness nodes supply different results; no new node is proposed.

## Not duplicates

No new node pairs to distinguish. In particular no duplicate of lem-weil-pbc-noetherian-finite-module-acc was created.

## Mathlib searches

The item's inherited Q54 searches remain intact as history. I also ran msearch.py for Q05 with leanfinder (two different natural-language phrasings), loogle 'PrimeSpectrum, Set.Finite', grep for finite-range/image plus Noetherian/irreducible, and leansearch for Noetherian induction and generic constancy. The exact query texts and actual summaries are appended in mathlib_searches and searches.jsonl. All services answered successfully.

Read the returned statements: PrimeSpectrum.instNoetherianSpace and finite_setOf_isMin give topology/finitely many minimal primes, not the finite range of an arbitrary function; IsNoetherian.induction is the general induction tool, not a one-line proof of the item. LocallyConstant.range_finite (Mathlib/Topology/LocallyConstant/Basic.lean:323) needs local constancy on the whole space, which is not assumed here. subsingleton_image_closure_of_finite_of_isPreirreducible (Topology/JacobsonSpace.lean:196) assumes a continuous closed map and already finite image, so cannot be used here. The linear-map finite-range results are unrelated module-finiteness statements. Reused the already searched maximality leaf instead of creating a new induction leaf. I read set_has_maximal_iff_noetherian in RingTheory/Noetherian/Defs.lean:155, whose quantifiers give exactly the needed maximal bad ideal.

## Review by Q05

I reviewed the split against delivery-errors B through E with the statements and sources open. For the item I read Stacks algebra.tex Tag 00IK, lemma-Noetherian-basic (especially its ascending-chain assertion and the proof's omitted equivalence), and more-morphisms.tex Tag 0ASY, lemma-generic-flatness-stratification (the final descending-closed-subset argument). The latter is only the source pattern; the maximal-bad-ideal finite-image proof is explicitly marked agent-written. No new nodes need source comparison. I also read the complete statements of def-weil-pbc-noetherian-ring, def-weil-affine-spectrum, def-weil-finitely-generated-module and lem-weil-pbc-noetherian-finite-module-acc.

Step 1 uses clause (2) of lem-weil-pbc-noetherian-finite-module-acc, which really says every nonempty set of submodules has a maximal member. Its hypotheses are met by the given Noetherian ring and M=A: def-weil-finitely-generated-module defines generation by finitely many elements, and the text explicitly verifies that 1 generates A. Ideals are exactly A-submodules of the regular module, so the theorem applies to the set of ideals with infinite F-image; no finite or chain assumption on that set is needed. The unit ideal has empty vanishing set because prime ideals are proper. This is the only non-elementary step, with an existing Mathlib leaf, and introduces the maximality used by all subsequent steps.

Step 2 cites def-weil-affine-spectrum only for its explicit assertion that points are prime ideals. It does not take a decomposition theorem from that definition. The text gives the product criterion for primality, proves each strict enlargement, and proves both inclusions in the two-set cover. Taking images under an arbitrary function preserves this union; finite unions are elementary. This establishes primality of I directly without radical-ideal, irreducibility, minimal-prime or quotient-spectrum theorems. That argument is under 800 characters, uses only definitions and step 1, and is elementary rather than a hidden lemma needing its own node.

Step 3 applies the item's own hypothesis only after I has been proved prime and proper. The chosen b is outside I, so I+(b) is strictly larger. The two cases b in p and b not in p give explicitly the inclusion F(I) subset {t} union F(I+(b)); finite subsets of finite sets give the contradiction. The step cites no node because it uses only the hypothesis, the previously established maximality and the displayed definitions of V and D. No continuity, open-image theorem or extension of values across a closure is invoked.

Step 4 discharges the counterexample assumption for all ideals J, then uses V(0)=Spec A for the full image. It explicitly checks the zero ring and empty target. Further small-case checks: for a field there are no bad ideals since its spectrum has one point; for A=k[e]/(e^2) the nonreduced structure does not affect the pointwise argument; for k[x,y]/(xy) the nonprime ideal (0) is treated by the two-branch cover using x and y; for k[x] the identity map on primes does not meet generic constancy on V(0), so the result falsely claiming every arbitrary map has finite range has not been smuggled in. A function with a distinct value at one closed point and a constant value elsewhere satisfies the hypothesis, illustrating that continuity is unnecessary. The proof does not need the target to be finite, inhabited in advance, or a topological space. If T is empty and f exists then Spec A is empty, and all required images are empty.

B1--B9: no new statement-only records, definitions or Mathlib leaf records were needed; the existing statement stays self-contained, its TeX and original definition references remain intact, the original source tags/labels are retained, and search records are actual commands rather than invented searches. B10: the project-source search found no exact attachment. C1--C4: the only non-elementary fact is exactly the statement of the maximality leaf; the citations.json extracts are verbatim parts of the three cited statements, checked by string inclusion. No node's proof is used as if it were its statement. C5--C8: searched the whole DAG and blueprint, added no duplicate and no new off-route non-leaf tool; the one off-unit theorem is already a Mathlib leaf and needs no tool-use approval. All other dependencies are definitions or references to earlier steps. D1--D5: the proof is the argument itself, not a relabelling into subordinate nodes; maximality is explicitly established before use and no induction hypothesis is left implicit. E1--E7: properness, nonempty bad set, finite generation and strict inclusions were checked at the steps just described; no added hypothesis, object change, transport assertion, source error or statement dispute is present. No proof step exceeds 2000 characters.

Corrections during this review: I made the zero-ring and empty-target cases explicit, wrote both inclusions for the prime-ideal cover, and stated that 1 generates the regular module so the exact finite-module hypothesis of the cited maximality theorem is visible. I left the unused 00FR source citation as inherited provenance, without claiming its result is used by a proof step. No work is left for a second worker.
