# Stage-1 delivery: lem-sfb-tame-extension-uniformizer-root-domination

Group Q49, 2026-10-24. Direct delivery by the assigned worker.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-tame-extension-uniformizer-root-domination.json`: statement item split into seven steps, using existing nodes only. The statement, statement dependencies, creation metadata and inherited blueprint provenance are preserved. New Mathlib searches were appended with their actual logged results.
- `citations.json`: one verbatim statement quotation for each node used by each numbered proof step (18 entries).
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The item itself is not a Mathlib leaf: the searches find unramified local criteria, ramification-index formulas and infinite-place ramification, not the existential tame domination theorem. LeanFinder was tried with two different formulations; LeanSearch, Loogle and the required grep were also run. The `RingTheory` grep returned no tame or Abhyankar matches. All five new searches are preserved verbatim from `searches.jsonl`, alongside the inherited Q80 searches.

## Attachments

None for the whole item. I searched `lean/WeilConjectures/` for the blueprint tag and for tame extensions and uniformizer roots, and read the root-algebra theorem and the compositum maximal-ideal theorem. `AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra` proves the root-DVR part only. The existing local Abhyankar declarations assume a specified local diagram rather than constructing the existential finite overfield of this item. Consequently they are inputs to a split, not an attachment claiming all clauses.

## WANTED

None. All literature used is present locally.

## Problems found and corrections

The item's statement agrees with Stacks 0EXW (1) implies (2), with the root-DVR and canonical residue description spelled out from 09EV. No statement dispute and no hypothesis or conclusion changed. There was no previous sandbox item or split to recover. No repair order exists for this item.

The useful existing tensor-factor theorems `lem-sbc-dvr-tame-tensor-factor-*` impose divisibility of residue degrees as well as ramification indices. That extra hypothesis is absent here and was not assumed. Instead the proof uses the existing compatible-normalization-diagram lemma and the two local Abhyankar lemmas, whose statements require only that the ramification index divides the chosen exponent and that the residue extension is separable. I explicitly accounted for primes above the closed point being maximal, so that the item's quantification over maximal ideals supplies every hypothesis of that diagram lemma. I checked Stacks tags against `tags/tags` and used 09E8 for `remark-finite-separable-extension`.

The source chooses the least common multiple and any generic tensor factor. A product of the finitely many branch indices is also a positive common multiple prime to p; choosing a root in an algebraic closure of T selects the concrete compositum T(a). This is the same root-extension/Abhyankar route, with the elementary construction and all field finiteness/separability assertions written out. No part of the conclusion was moved to a new node.

## Blueprint and searches for existing results

I read the chapter and unit records, SETUP's three levels, the latest blueprint unit and its direct-images proof (3). As the inherited provenance already explains, the newest direct-images proof no longer contains the historical auxiliary Epp argument; this supporting item still has its explicit Stacks source. The inherited `blueprint.from.node=null`, exact historical place and via chain remain intact. No chapter or unit was edited.

`tools/blueprint_refs.py ancestor` returns null for this item. Whole-blueprint searches were run for `uniformizer`, `tamely ramified`, `Abhyankar`, and `root of a uniformizer`; the latter three return no matches. The broad uniformizer hits concern coefficient DVRs or different ramification statements. I searched the entire DAG by 0EXW, 09EV, 0BRM and key concepts, and opened the statements of the local diagram, normalization-structure, root-DVR, local residue and maximal-ideal, tensor-factor, finite-normalization and field-separability nodes. Existing nodes cover all inputs; none other than the item states its whole existential conclusion.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. Existing stronger or differently scoped results are cited in place.

## Review by Q49

I read `more-algebra.tex`, 0EXW `lemma-characterize-tame`, including the entire implication (1) to (3), 09EV `lemma-pull-root-uniformizer` and its quotient-ring proof, 09E8 `remark-finite-separable-extension`, and the local cancellation argument of 0BRM with the 09E7 criterion. These give the intended route without a henselianity, completeness, excellence, or perfect-residue-field assumption. There are no new nodes requiring separate sources. I checked B through E of delivery-errors against the final files: the item is self-contained, its statement cites its notions, its proof gives the argument, and each non-elementary input is an existing node whose statement is quoted verbatim in citations.json.

Step 1 uses the PID Noetherian/normal statement, the finite-separable integral-closure finiteness statement, and the normalization-structure statement with the identity map R to R and finite P=T. Their hypotheses hold since R is a DVR and T/F is finite separable. The identity specialization supplies the finite nonempty set of branches and the local DVRs; finiteness of C as an R-module is obtained separately, rather than incorrectly taken from a statement asserting only Noetherianity. Taking a product rather than a least common multiple is elementary and preserves prime-to-p invertibility and all required divisibilities.

Step 2 uses the algebraic-closure existence statement, the definition of separability of a polynomial by a Bezout identity, and the definition of the minimal polynomial as generator of the evaluation kernel. I checked the displayed identity for X^m-pi and differentiated f=gh to give the Bezout identity for the minimal polynomial explicitly. This justifies separability of the chosen element without an unrecorded polynomial theorem. The algebraic closure is of T, so the selected root and T really lie in one field.

Step 3 uses the generated-scalar-extension statement with K=F, M=T and the singleton consisting of the root, then algebraic separability transitivity and separability after enlarging the intermediate base. Each cited statement has exactly these hypotheses. The finite spanning set and the injective/surjective multiplication argument show that T[a] is a field and that T'/F and T'/F_m are finite; these are elementary finite-dimensional linear algebra, not an assumed compositum theorem.

Step 4 uses precisely the domain/DVR/maximal-ideal conclusion of the root-algebra node. That statement does not give the fraction field or residue identification; those are proved here. The evaluation map is injective because a nonzero prime in this DVR contains the uniformizer and hence pi, whereas evaluation is injective on R. Monic division gives the finite free basis. The quotient by the root is explicitly R/(pi), so the identification with k is canonical and the index is m. I checked m=1 rather than applying a source lemma stated only for m at least two.

Step 5 again uses PID normality and finite-separable normalization finiteness, now over the actual root DVR R_m and with T'/F_m, whose hypotheses were established in steps 3 and 4. Integral maximal contraction says every maximal h lies over the root maximal ideal. Its residue field is finite because it is a quotient of H modulo the extended base maximal ideal, a finite-dimensional k-vector space. The algebra-generation hypothesis for the next step is checked as R_m[T]=T[a]=T'.

Step 6 applies the compatible local-diagram statement to the exact rings and fields written in the proof. I checked all of its quantifiers and finiteness assumptions against steps 1, 3, 4 and 5. Its condition on primes above the base maximal ideal follows from the item's condition on maximal ideals using the integral-prime-over-maximal statement, whose full statement was opened and quoted. The diagram supplies the DVR localizations, both fraction fields and the local map U to V, not merely a diagram of abstract fields. It imposes no residue-degree divisibility. This corrects the tempting but invalid use of the more restrictive tensor-factor statements.

Step 7 uses the two local Abhyankar statements separately: the first gives the extended-maximal-ideal equality, the second gives residue separability. I checked finite faithful R to R_m, the two index equalities, invertibility and divisibility of e_i, separability of the branch residue field, the generation of T', both fraction fields and commutativity/locality of the map U to V. All are precisely the conclusions of earlier steps. Finite residue degree is supplied by step 5; the localization residue field is identified with H/h by reducing each fraction. The arbitrary choice of h proves the assertion at every branch, not just at a selected one.

I tested the edge cases T=F, all e_i=1, m=1, a non-henselian R with more than one branch, mixed characteristic, and imperfect k with finite separable branch residues. The construction gives T'=T and R_m=R when m=1; multiple branches are all absorbed by the product m. Wild ramification (p dividing an index) is correctly excluded, since the displayed separability identity and local cancellation would fail. A nonseparable residue extension is also excluded. The source and proof never assume that the residue field is algebraically closed.

All seven steps are shorter than 2000 characters. I checked that none of the cited nodes has a dependency path back to the item, using a read-only traversal of the current DAG. The four off-unit generic algebra tools are declared in `split_report.tool_uses`, with their purposes. No second reader or sub-agent was started; no Lean was written or compiled, no local DAG checker was run, and all writes are inside the assigned sandbox.

## Unfinished work and validation

No mathematical part is left unresolved. The server `review_split` check has passed. The required delivery dry run and push are the remaining validation/delivery steps; their results are recorded below after execution.
