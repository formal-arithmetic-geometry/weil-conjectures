# Stage-1 report: lem-sfb-flat-quotient-ideal-fibre-regularity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-quotient-ideal-fibre-regularity.json: item, statement, split into five steps; not a Mathlib leaf.
- citations.json: eleven verbatim statement excerpts, one for every node used by every step.
- searches.jsonl: five searches performed with the prescribed msearch command, read and recorded in the item. The imported searches remain intact.

No new nodes, definitions, or Mathlib leaves. No Lean files were written and no compiler or Lake command was run.

## Attachments

None for this item. Searching WeilConjectures/ for the blueprint tag returned no occurrence. Concept searches found RingTheory.Sequence.isRegular_and_flat_quotient_of_closedFiber in WeilConjectures/RingTheory/RegularSequenceFlatClosedFiber.lean: it lifts a specified regular list and proves flatness of prefix quotients, but does not give the ideal-generation equivalence, especially the forward implication. It belongs to the already-existing lem-weil-pbc-grothendieck-regular-sequence-flat, not this item.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and decisions

The statement is unchanged and no statement dispute was found. The item had no proof. Its source named the correct route, but each of its non-elementary inputs now has an explicit node citation. I did not use lem-pur-relative-regular-equations-base-change or lem-pur-flat-quotient-fiber-regular-sequence: both assume finite presentation, whereas the item expressly does not. Instead, the existing lem-pur-quasi-regular-flat-quotient-base-change has no finite-presentation hypothesis, exactly as Tag 0CEP requires.

The blueprint_refs ancestor command returns None for this inherited chain. I retained that null ancestor, the filled place, and the whole via chain, rather than inventing a different ancestor. I read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its proof, especially sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), which is the existing chain's direct-image branch. This local algebra split continues that supporting route. The four non-Mathlib algebra tools from other units are declared, with reasons, in split_report.tool_uses; they do not replace a step of the unit.

DAG searches by tags 00MG and 0CEP and by regular-sequence, quotient-tensor, and Nakayama keywords found all the needed nodes. Whole-blueprint searches for regular sequence, flat quotient, and closed fibre found no blueprint node stating the item. Mathlib searches used leanfinder twice, loogle, leansearch, and grep; the returned flat-ascent and faithfully-flat-ascent lemmas in Mathlib/RingTheory/Regular/Flat.lean (lines 38-49 and 86-94 read) require a flat map from the ring carrying the sequence. They cannot be applied to T -> T/mT in general. LeanSearch's Nakayama generator theorem covers only a supporting step. None gives the entire item.

## Not duplicates

No new nodes were created. The existing graded-polynomial, quasi-regular base-change, quasi-regular-to-regular, tensor-injectivity, quotient-tensor, Nakayama, and Grothendieck lifting nodes are reused directly.

## Review by NL

I read Stacks more-algebra.tex Tag 0CEP, label lemma-relative-regular-immersion-algebra, including its proof. Its first assertion concerns quasi-regular sequences and requires flatness of the final quotient over the base; it does not require finite presentation or flatness of the map to the new base. I also read algebra.tex Tag 00LN, label lemma-regular-quasi-regular, and Tag 061S, label lemma-quasi-regular-regular, so that conversion to and from the canonical graded-polynomial isomorphism is justified with exactly the local Noetherian and maximal-ideal hypotheses available here. For the converse I read Tag 00MG, lemma-grothendieck-regular-sequence, including its induction from 00MF; Tag 00HL, lemma-flat-tor-zero; and Tag 00DV, lemma-NAK, parts (2) and (8). All tags and labels were checked in the source/tag map. There are no new-node sources to audit.

For step 1, def-weil-pbc-noetherian-ring says that every ideal is finitely generated. Images of generators of the preimage ideal prove the quotient assertion directly. The elementary maximal-ideal correspondence shows that T/mT is local with maximal ideal n/mT; locality of A -> T ensures mT lies in n, so the quotient and its quotient by the image of K are nonzero. This step is genuinely elementary and does not appeal to a hidden Noetherian descent lemma.

For step 2, I opened all four cited statements. lem-pur-regular-sequence-graded-polynomial gives the canonical graded isomorphism, not merely freeness of the conormal module. lem-pur-quasi-regular-flat-quotient-base-change gives precisely preservation of that canonical isomorphism under arbitrary base change, with final quotient flat, without finite presentation. lem-weil-pbc-tensor-quotient-base-change gives the ring isomorphism T/mT -> T tensor_A k and its formula on generators. lem-pur-quasi-regular-noetherian-local applies to the resulting canonical isomorphism because the quotient ring is nonzero, local, Noetherian, and every equation lies in its maximal ideal. These are the exact properties its statement asks for, not content borrowed from its proof.

For step 3, lem-weil-pbc-flat-quotient-tensor-injective asserts exactness after tensoring any short exact sequence whose final module is flat. Here the exact sequence is the ordinary inclusion of K into T followed by the quotient, and its final module is A-flat by the item hypothesis. lem-weil-pbc-tensor-over-quotient-ring, clause (1), gives (A/m) tensor_A M = M/mM for both M=K and M=T with the stated formula. The map's image and kernel are computed explicitly, proving K/mK = bar K. This avoids the false general identification of K/mK with its image without flatness. Compatibility with the bar T action follows directly from the formula x -> x mod mT; the equality mK=(mT)K is expanded in the step.

For step 4, the coefficients of a finite combination in bar T lift to T, so subtraction puts the residual element in mK, proving K=J+(mT)K. Noetherianity makes K finite and hence K/J finite, by the images of the same finite generating set. lem-weil-pbc-nakayama-jacobson states exactly that a finite module M with IM=M vanishes for I in the Jacobson radical. In the local ring T the radical is its unique maximal ideal n, and mT is contained in it. Thus the lifted equations really generate the original ideal; they are not merely regular elements in K.

For step 5, lem-weil-pbc-grothendieck-regular-sequence-flat explicitly assumes a flat local map of Noetherian local rings, and assumes regularity of the given list modulo the extended maximal ideal. All these are the original hypotheses or the selected regular generators, so it gives regularity of that same lifted list. I do not use its additional prefix-flatness conclusion. def-weil-pbc-regular-sequence includes nonzero final quotient; properness of K and of bar K supplies this, including the empty-list case.

I checked B1-B10: no new statement nodes, no duplicate notions, no new unstated terminology, readable TeX, source tags/labels, real search results, and no whole-item project attachment. For C1-C8 every non-elementary fact used has the cited statement that supplies it, all those statements were opened, verbatim quotes are in citations.json, and the off-unit uses are declared as generic tools. For D1-D5 the actual ideal-lifting and Nakayama argument is retained in the item; neither implication is moved into a new node. Each step is below 2000 characters, so none hides a long argument. For E1-E7 I checked the hypotheses separately for each map: flatness of A -> T is used for 00MG, whereas flatness of T/K is used for tensor injectivity and 0CEP; neither licenses flatness of T -> T/mT.

Small cases: for K=0 the empty list works and tensor injectivity/Nakayama remain valid. If bar K=0, the proof forces K=mK and then K=0, so the reverse empty case is sound. If A is a field, m=0 and the criterion is tautological. For A=T=k[epsilon]/(epsilon^2) and K=(epsilon), removing the flat-quotient hypothesis would make the criterion false: bar K=0 but (epsilon) cannot have a regular generating list, since every nonzero element of the maximal ideal is a zero divisor. The example confirms exactly why flat quotient is needed for the ideal reduction identification. The condition K subset n excludes the unit ideal and hence the zero final quotient, in agreement with the regular-sequence definition. Nothing assumes A -> T finite type or finitely presented.

## Unfinished work

None in the one-level split. Existing cited statement nodes retain their own independently tracked proof work. Delivery checks follow this report.
