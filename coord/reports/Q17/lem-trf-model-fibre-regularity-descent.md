## Worker report

Q17, stage 1, 2026-10-23. Item: lem-trf-model-fibre-regularity-descent.

Files written: dag/nodes/sec-trace-formula/lem-trf-model-fibre-regularity-descent.json (the item, split into seven steps), citations.json (13 literal node-statement quotations), and this report. searches.jsonl contains the six actual Q17 search results. No repository file, launcher file or Lean file was written, and no compiler or build was run.

## New nodes

None. All non-elementary inputs were already nodes. There are zero new Mathlib leaves.

## Attachments

No attachment for the item: the upstream tag search returned nothing. Concept searches in WeilConjectures/RingTheory and AlgebraicGeometry found FibreLocalRingNaturalIso, CompleteLocalBaseChangeFiber, RelativeComponentFlatApprox and the NoetherianLocalModelTowerFiber family. I read the relevant declarations: the first supplies only the natural local-ring identification, the second assumes complete local rings and a surjective base map, and the others address approximation/flatness at stages. None gives every clause of this item with its arbitrary ring-map hypotheses. The existing Ideal.Fiber.localRingHom_surjective_ker_quotientEquiv at lean/WeilConjectures/RingTheory/FibreLocalRingNaturalIso.lean:45 is reused through its existing node, not claimed as an attachment for this item.

WANTED: none.

## Findings and Mathlib searches

The imported statement is correct; its text and statement dependencies are unchanged. No statement dispute was found. The source's short assertion that the model fibre local ring maps faithfully flatly to the original one requires spelling out the induced residue-field extension, the tensor comparison, and the correspondence of primes. These are now explicit. No flatness assumption on A_0 to A, finite presentation or Noetherian condition has been added.

I read the six inherited search records and their returned declarations, retained them, and ran six Q17 searches with msearch.py: two LeanFinder phrasings, Loogle, LeanSearch, and two source grep queries. All services answered successfully. The search log and the node contain exactly the query texts that ran. The source of Mathlib/RingTheory/Regular/Flat.lean shows that IsRegular.of_faithfullyFlat_of_isBaseChange is ascent, not the descent needed here. The localization and faithful-flat base-change hits supply individual inputs, not the full item. Their existing DAG nodes are reused. Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean and Flat/Localization.lean were read, as were RingHom/Flat.lean and FaithfullyFlat/Basic.lean. There is no exact whole-item Mathlib match.

DAG searches used ids/concepts for fibre-stalk quotients, fibre-ring-local identifications, flat local maps, field-extension base change and faithful-flat universal injectivity. The search distinguished lem-weil-pbc-fibre-ring-local-ring-natural-iso from the weaker abstract-isomorphism node. blueprint_refs.py ancestor gives lem-trf-local-term-locality. Whole-blueprint searches for faithfully flat, fibre local, regular singleton and nonzerodivisor found no exact item duplicate. The latest chapter, sk-i-curve-zero and lem-trf-local-term-locality texts were read. The item retains its recorded historical 057K/057S/055W/0570/056Y lineage; this split is pure commutative algebra and does not replace a chapter or unit argument. The natural fibre-ring isomorphism is declared as a generic tool in split_report.tool_uses; no maintainer-owned top-level tool_uses field is written.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to distinguish. In particular I did not create a second flat-local faithful-flatness lemma, fibre quotient lemma or nonzerodivisor-descent node.

## Review by Q17

I read Stacks more-morphisms.tex, Tag 056Y, label lemma-slice-given-element, statement and all three proof paragraphs (lines 6166–6261). The second paragraph is the precise source of the item: after a cartesian model and a descended h_0 are fixed, the fibre local ring is a localization of the model fibre local ring tensored with the residue-field extension. It explicitly uses a flat local map, faithful flatness, membership of h_0 in the maximal ideal and descent of its nonzerodivisor property. I also read algebra.tex Tag 00E6 (remark-fundamental-diagram), 0H9M (remark-local-ring-fibre), 00HI (lemma-flat-base-change), 00HT (lemma-flat-localization), 00HR (lemma-local-flat-ff), 00HB (definition-flat), and 05CK (lemma-faithfully-flat-universally-injective). No SGA source is used. There are no new-node source statements to review.

Step 1 cites def-weil-pbc-localization-at-prime, whose statement gives both prime localization fractions and the residue field. I checked the contracted-prime equality: denominators outside p_0 stay outside p, and the induced residue-field map has zero kernel because a numerator dies exactly when it is in p_0. This is an elementary fraction construction, not an unsupported field-map assertion.

Step 2 cites def-weil-pbc-module-tensor-product for its universal property, balancing relations and pure-tensor generators. I checked the displayed map and inverse on ((t tensor b_0) tensor lambda) and ((b_0 tensor lambda_0) tensor lambda). Balancing moves t to its image in k and lambda_0 along k_0 to k, so both composites fix these generators. Multiplication and the k-structure are preserved. This routine generator calculation is written in the step, rather than made into a new node.

Step 3 cites lem-weil-pbc-fibre-ring-localization-quotient, which actually states the B-algebra identification with (A minus p)^(-1)B modulo p and its fraction formula. The localization definition supplies residue fields. I checked the fibre-prime construction by the map to kappa(q): p dies there and every denominator from A minus p survives. Every fibre element has a numerator/denominator presentation; membership in the kernel is exactly numerator membership in q. For any prime of this fibre contracting to q, the same test holds, since the denominators are units. The contraction r_0 consequently lies over q_0, with no surjectivity assumption on A_0 to A.

Step 4 uses four statements, all opened and read. lem-weil-pbc-field-extension-base-change-faithfully-flat says exactly that D to D tensor_K K' is faithfully flat for any commutative K-algebra D; its hypotheses hold for D=E_0 and the field map of step 1. def-weil-pbc-faithfully-flat-ring-map includes that faithfully flat implies flat. lem-weil-pbc-flat-local-ring-maps gives the flat local map at a prime and its contraction; its first conclusion requires no Noetherian assumption (the later optional Noetherian clause is unused). lem-weil-pbc-flat-local-hom-faithfully-flat then applies to those prime local rings. In particular I checked that it is not valid merely to assert that a localization of a faithfully flat target stays faithfully flat globally: we use locality at the contracted primes and 00HR.

Step 5 uses lem-weil-pbc-fibre-ring-local-ring-natural-iso, whose statement includes the actual fraction formula, surjectivity, kernel and induced quotient isomorphism. I checked the primes supplied in step 3 meet its hypotheses for both A to B and A_0 to B_0. The natural fraction formula sends a_0 to the same element by either route. The weaker abstract-isomorphism node would not suffice; it is not cited. I read the existing completed upstream theorem at line 45 as well. This is the only non-Mathlib generic tool used from another unit.

Step 6 cites lem-weil-pbc-faithfully-flat-universally-injective, whose statement is the injectivity of N to N tensor_R S, not merely a definition or a spectrum-surjectivity assertion. I specialized N=R=C_0 and identified C_0 tensor_C_0 C with C by the displayed map and inverse, using the tensor definition. Injectivity of multiplication is then descended by the written element argument. No flatness-preserves-exactness lemma or unstated regular-sequence descent theorem is hidden here.

Step 7 uses only the already cited localization definition and def-weil-pbc-regular-sequence. The first identifies the maximal ideal as r_0 C_0; the second requires BOTH injective multiplication and nonzero quotient. I checked a_0 is in q_0 because i(a_0)=a is in q, hence its image is in r_0. Containment of the principal ideal in the proper maximal ideal makes the quotient nonzero. This is elementary, with the full argument written out.

Small cases: identity base change makes the fibre comparison the identity. For the nonflat map Z to F_p, take B_0=Z[T], B=F_p[T], q=(T) and a_0=T: k_0=k=F_p, both stalks are F_p[T]_(T), and the conclusion holds, confirming that the argument does not inadvertently assume flatness of the original base map. In a field stalk the only allowed a is zero, so the injective-multiplication hypothesis fails; the conclusion is not incorrectly claiming a regular zero singleton. For k[epsilon]/(epsilon^2) at (epsilon), the element epsilon fails the same hypothesis. A unit is excluded by a in q, which is essential for the nonzero quotient. A zero B has no prime q and is outside the quantified data. All arguments allow non-Noetherian rings and arbitrary, including inseparable, residue-field extensions.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files: no new statement-only node or hollow definition, no new source/definition gap, no relabelled item clause, no forward citation or circular induction, and no unexpanded transport/denominator argument. Every cited node supplies the clause taken from it; citations.json contains all 13 use entries verbatim. Every proof step is below 700 characters, hence no long step hides a lemma. The source statement remains intact. The preliminary server review_split returned PASS with zero new nodes. I corrected a TeX prime notation during this reading; no mathematical correction or statement weakening was needed.

## Unfinished work

None within this stage-1 split. The delivery still requires the mandated final preflight and push, whose result is recorded by the delivery tool.
