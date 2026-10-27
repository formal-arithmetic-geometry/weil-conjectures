# Q60 stage-1 delivery: lem-per-regular-map-finite-surjective-detection

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-map-finite-surjective-detection.json`: statement, split; retained the imported statement, source, provenance, and earlier Mathlib searches. Added six proof steps and their exact dependencies, current searches, and blueprint/tool-use explanations.
- `citations.json`: eleven step/node entries with verbatim quoted statements.
- `report.md`: this report. No new DAG nodes; no new Mathlib leaves.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, geometric regularity, regular ring maps, and regularity/surjectivity did not find an exact declaration for the item. `RingHom.isRegular_of_isRegular_comp` in RegularPermanence.lean concerns a faithfully flat extension of the target ring, not a finite surjective extension of the base ring, so is not an attachment. Existing project results are used through their DAG statements. No Lean files or build outputs were written.

## WANTED

WANTED: bibliographic integration of Silvio Greco, *Two theorems on excellent rings*, Nagoya Mathematical Journal 60 (1976), 139–149, DOI 10.1017/S0027763000017190, into literature/LIST.md and literature/. This request was already present in the item's source provenance. I read the publisher scan through https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf, printed pp.139–140, Definition 1.1 and Proposition 1.2. The publisher URL timed out; direct download of the mirror into the sandbox was refused with HTTP 403. The proof's expanded ingredients are all in the local Stacks source.

## Findings and scope

The initial node had no proof. Its statement agrees with Greco's converse, specialized to geometric regularity; no statement dispute or correction is needed. Greco assumes commutative Noetherian rings globally, explicitly recorded on printed p.139. His fibre equality is precisely the equality expanded here. His reference to geometric-regularity descent is expanded using the common-field argument in Stacks Tag 038W, `varieties.tex`, `lemma-geometrically-regular-upstairs`; regularity upstairs is Algebra Tag 0381, `lemma-geometrically-regular`, and regularity downstairs is Algebra Tag 07NG, `lemma-descent-regular`.

I deliberately use the common-field argument directly rather than introduce another lemma asserting descent of geometric regularity. This avoids a node that would merely move the central content of the item elsewhere. In this argument L/k can even be arbitrary: a finite test extension K/k has a compositum finite over L. Thus the given finiteness of R'/R is retained in the statement but need not be used to prove residue-field finiteness. Surjectivity on spectra and the assumed flatness of u are used exactly where needed. We never assert R -> R' is flat.

I read the latest blueprint's chapter, unit statement, and ancestor proof (lem-per-artin-gabber-affine-curve, Step 3); the inherited auxiliary provenance passes through the quasi-excellence/completion chain. This split expands that chain's Greco input. No chapter or unit record changes. Whole-blueprint searches via blueprint_refs.py for 'geometrically regular', 'regular ring map', 'finite surjective', and 'geometric regularity' found no statement equivalent to this item. The eight finite-surjective hits concern curve degrees, pullback descent, or symmetric products. Whole-DAG keyword/title searches identified all reused algebraic inputs; no new node is needed. The general algebraic inputs from other units are declared in split_report.tool_uses for the maintainer's review.

## Not duplicates

No new nodes. Existing field-compositum, tensor-cancellation, field-extension faithful-flatness, regularity-test, and regularity-descent nodes are reused.

## Review by Q60

I read Greco's Proposition 1.2 and Definition 1.1 from the publisher scan, then the actual local Stacks proofs at `algebra.tex` lines 47104–47148 (0381) and `varieties.tex` lines 2471–2505 (038W). I also read the common-extension proof in `fields.tex`, label lemma-common-extension-field (0H7K), and its compositum definition, label definition-compositum (09ID). There are no new statements to compare with sources.

For step 1 I opened def-weil-pbc-localization-at-prime and def-weil-pbc-g-ring. The former defines precisely the two fibre rings and residue fields used, and the latter says regularity of u' gives Noetherian geometrically regular fibres. The residue map is written on fractions, including the check that denominators stay nonzero because the chosen prime contracts to p. This is elementary from the given prime equality; it does not use a finiteness-of-residue-fields theorem.

For step 2 I opened lem-weil-pbc-tensor-cancel-base-change, whose statement gives the algebra isomorphism and its inverse. Two cancellations and factor interchange give the displayed isomorphism; the step spells out both maps. Their balancing and composites are checked on pure tensors, so no additional comparison lemma is hidden here.

For step 3 I opened lem-weil-common-extension-fields and lem-weil-pbc-compositum-degree-bound. The first supplies embeddings into a common field with agreement on k; the second explicitly supplies finiteness over L because K/k is finite. I do not take the arbitrary common overfield itself to be finite. Identifying the fields with their embedded images is legitimate because the maps are embeddings. A finite basis supplies field generators, as required by the next step's hypothesis.

For step 4 I opened lem-weil-pbc-geometrically-regular-finitely-generated-extensions: its hypotheses are a Noetherian geometrically regular algebra over a field, and its conclusion is a Noetherian regular tensor product for every finitely generated field extension. Here they hold for D over L and M/L. Tensor cancellation is cited again, and both maps identifying this ring with (K tensor_k C) tensor_K M are displayed. In particular M is not assumed finite over K, which is unnecessary.

For step 5 I opened lem-weil-pbc-field-extension-base-change-faithfully-flat and lem-weil-pbc-regular-ring-faithfully-flat-descent. Their statements apply to the K-algebra E and arbitrary field extension M/K, and then to the resulting faithfully flat map with regular target. Descent includes Noetherianity, so taking K=k establishes the Noetherian prerequisite for the geometric-regularity definition, rather than assuming it without a citation. The remaining test extensions are exactly the finite purely inseparable ones in def-weil-pbc-g-ring. Step 6 uses that same definition together with the already assumed flatness, and is elementary assembly.

I checked the empty-spectrum case R=0 (the fibre requirement is vacuous), the zero fibre C=0 (tensor products remain zero and regularity/descent are still applicable), the identity base change, and purely inseparable extensions in positive characteristic. No separability or reducedness of R' is assumed. The characteristic-p test is the reason to test every K/k, rather than descend only ordinary regularity of C. All steps are below 700 characters; none reaches the 2000-character long-step threshold. Every cited node's entire statement is quoted verbatim in citations.json, and no statement is used for information existing only in its proof. No new elementary or duplicate nodes were introduced. Mathlib search hits on regular sequences or geometric reducedness were read and rejected as different notions; all new recorded queries are real msearch.py log entries. Nothing remains unfinished in the split.
