# Stage-1 delivery: lem-sfb-semilinear-sylow-snc-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-sylow-snc-resolution.json: existing statement split into six steps; no statement change; no Mathlib match for the complete assertion.
- citations.json: one verbatim statement quotation for every citation in every proof step.
- report.md: this report.

No new nodes and no new Mathlib leaves. searches.jsonl records five actual msearch.py calls. ilo.txt is a local text extraction of the supplied PDF, not a delivered project file.

## Attachments

None. Searches for the exact blueprint tag and semilinear/Sylow/normal-crossings terminology in lean/WeilConjectures found no declaration proving the item. The existing curve Sylow-cover statements concern different objects and do not give a projective SNC resolution of a semilinear scheme quotient. No declaration was treated as proved merely because its statement exists.

## WANTED

None. The ILO volume, Stacks source, current blueprint, and referenced DAG nodes are available in the read clone.

## Corrections and route

The imported item had no proof and its stmt_deps omitted most definition ids explicitly cited in its statement. I supplied the assembly proof and included every such id in stmt_deps. I retained the statement, source, existing searches and all provenance fields.

Two existing sibling results already give the substantial inputs: lem-sfb-semilinear-sylow-good-components and lem-sfb-tame-snc-quotient-resolution. I reused them rather than creating weaker copies. In particular, I did not infer that every component of an arbitrary Sylow quotient has prime-to-ell generic residue degree: selection is provided by the good-component lemma. The resolution lemma is applied only after selection, with its separate invertible-order hypothesis checked. No statement dispute was found.

The inherited blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor. Its place is already specified and is retained. The current direct-image proof paragraph (3) and the chapter/unit records were read; this input continues the existing alteration/tame-boundary reduction below that route. Blueprint searches for Sylow, semilinear, normal crossings, log smooth and quotient found no imported node stating the item. No chapter or unit record is changed. The off-unit statement citations are already Mathlib leaves (Sylow existence and restriction of smoothness), so no new generic tool approval is needed.

## Searches and reuse

In the original split there was no earlier sandbox item or report to resume. This repair resumes that retained split and reuses its logged searches after reading their results; it adds no search record. The live item already records its producer's five searches, which remain untouched. The original split also ran the required msearch.py commands with the item id, read the returned hits, and appended their actual queries and outcomes:

- leanfinder, full semilinear/Sylow/SNC statement: Frobenius/invariant-ring arithmetic and generic residue-field facts; none constructs the required resolution.
- loogle, `Sylow, AlgebraicGeometry.Scheme`: zero hits.
- grep, `normalCrossing|normal_crossing|semilinear.*quotient|Sylow` in AlgebraicGeometry: zero hits.
- leansearch, Sylow quotient resolution with boundary: Sylow group theory declarations, not the geometric assertion.
- leanfinder, second phrasing about tame quotient singularities and projective birational resolution: standard-smooth algebra and local smoothness declarations, not the quotient-resolution assertion.

Both semantic phrasings were run, and no unavailable call was described as an absence result. All five calls in this attempt were available. No new node requires further searches or duplicate-tag distinctions.

## Not duplicates

No new nodes. The pre-existing good-component selection and tame quotient resolution were used as dependencies, not copied. The elementary restriction and set-image arguments remain proof steps.

## Review by Q109

I read ILO Expose X 2.3 Step 2 and diagram (2.c), printed p.151, and Step 3, pp.151--152, in the supplied PDF text, together with the relative SNC definition following X 2.1 on p.149. Step 2 of the source factors the model through a Sylow quotient; Step 3 explicitly handles a connected component and its stabilizer modulo generic inertia, then induces over component orbits and resolves the quotient logarithmically. The two existing sibling nodes package these distinct parts, so using both retains the source's argument. I did not substitute the existing trait-only logarithmic modification node, whose base hypothesis would not apply to a field.

For step 1 I opened lem-weil-pbc-sylow-subgroup-prime-index. Its statement gives existence of a prime-power subgroup and prime-to-prime index for every finite group; the hypotheses here are exactly finite G and prime ell. This is the existing Mathlib leaf. I use neither conjugacy nor an effective action at this step.

For step 2 I opened the entire statement of lem-sfb-semilinear-sylow-good-components. It takes the same finite extension K/e, radicial fixed-field condition, normal proper componentwise integral base, smooth projective semilinear model, invariant projective surjection, finite generic residues, all subgroup quotients, and dense-open full-quotient condition as this item. Its conclusion explicitly supplies finite Galois K/F, prime-to-ell [F:e], a clopen union meeting every generic fibre, the projective surjection d and every retained component's prime-to-ell residue degree. It also explicitly supplies the clopen inverse image and finite quotient restriction. Thus I use its statement, not a construction hidden in its proof. Finite Galois implies finite separable by the terminology stated in that node. The factorization dq is the given induced quotient factorization restricted to the selected part.

For step 3 I opened lem-weil-pbc-smooth-restrict-open-subschemes and read Stacks morphisms.tex Tag 01V6, label lemma-smooth-characterize, especially its final open-restriction assertion; Tags 01VA and 01VC were also checked against the tag table. Part (a) gives smoothness of Ycirc over K. I opened def-weil-closed-immersion, def-kun-projective and def-trf-smooth-strict-normal-crossings-divisor. The closed-embedding argument is written out using the topology and surjective structure sheaf map: restriction to a clopen piece is projection over the two disjoint open parts, so the restricted projective embedding remains closed. This uses clopenness, not the false assertion that arbitrary open subsets of projective schemes remain projective. Each integral D_i is either wholly retained or wholly discarded; retained intersections have the same local rings and codimensions, while the empty-index intersection is the smooth Ycirc. The reduced and Cartier conditions restrict locally. These are the exact conditions of the cited relative-SNC definition. This step uses a smoothness theorem, so it is marked non-elementary rather than presenting the whole restriction argument as an unsupported elementary assertion.

For step 4 I verified that L-invariance of Ycirc comes from the quotient preimage, L-invariance of Dcirc comes from h and C, and the F-linearity of the action comes from L fixing F. The characteristic of F is that of e and |L| is a power of ell, so its image is nonzero and invertible in the field F. This direct field calculation allows a nonfaithful action, including L acting trivially on K. The categorical quotient's F-structure agrees with the descended one in step 2 by its defining factorization. No assumption of a faithful L-Galois action on constants is introduced.

For step 5 I opened the entire statement of lem-sfb-tame-snc-quotient-resolution. It explicitly permits disconnected Y, nonfaithful actions on both Y and K, and empty divisors. It assumes a finite separable K/F, invertible group order, a smooth projective K-scheme with semilinear F-action, an invariant relative SNC divisor, and the supplied finite categorical geometric quotient. Steps 2--4 verify those hypotheses for Ycirc, Dcirc and q. Its conclusion explicitly includes a smooth projective F-scheme R, a projective surjective F-morphism v to the quotient, unchanged component generic residue fields, the reduced SNC divisor supported on v inverse image of q(Dcirc), regularity, boundary and parameter assertions. No regularity-over-an-imperfect-field inference is imported separately: the cited lemma states the required relative smoothness and regularity themselves.

For step 6 I checked both inclusions in q(|Dcirc|)=d inverse image of C, using exactly h=dq and surjectivity of q. Pulling that identity back along v proves the requested equality. No hidden image/base-change or non-elementary quotient theorem is used. Reduced inverse image and the original inverse image have the same support by the definition of reduction.

For the delivery-errors B--E check: the only written node is the existing item, all its objects and meanings remain self-contained, its TeX is unchanged, and its full definition-reference list is now present. There are no statement-only new nodes with hidden proofs, no copied clauses, no duplicate new statements and no unrun searches. Every non-elementary step cites a statement that explicitly supplies the fact used; the full statements are copied verbatim into citations.json. The proof dependencies are exactly the union of step citations. The two principal results are siblings created under the global alteration item and do not cite this item; the remaining cited definitions and Mathlib leaves also introduce no reverse dependency. No step exceeds 2000 characters or hides a new long lemma.

I tested empty C (D and Dcirc empty, hence E empty), trivial G, nonfaithful actions on constants and schemes, disconnected Y and B, and zero-dimensional components (where a relative effective Cartier SNC boundary is empty). Selection still meets every generic fibre, and the argument never asks the discarded quotient components to have prime-to-ell degrees. No missing hypothesis or false edge-case statement was found. No Lean file was written and no compiler or Lake command was run.

## Repair of the returned delivery (2026-10-23)

The return at branch head ee4ff9a336b, dated 2026-10-22 14:48 UTC, has one point: the independent reader approved the proof, but landing refused the side completion because it had not been promoted into the live DAG. I continued the retained sandbox rather than replacing its proof or repeating its searches. The current read-clone item is still unsplit, with the same statement and source; it has no released stage-1 repair note. Its differences from the retained item are the split-owned proof, proof dependencies, completed statement dependencies, search additions, status and split report. The delivery command rebuilds the commit on current origin/sheaf-dag and preserves current maintainer metadata. The required initial dry run exited successfully at 0bcb005ee4b before I edited the repair.

I reopened all seven cited node files in the current DAG, comparing their full statements with the full-statement quotations retained in citations.json. Every quotation still agrees verbatim: lem-weil-pbc-sylow-subgroup-prime-index; lem-sfb-semilinear-sylow-good-components; lem-weil-pbc-smooth-restrict-open-subschemes; def-weil-closed-immersion; def-kun-projective; def-trf-smooth-strict-normal-crossings-divisor; lem-sfb-tame-snc-quotient-resolution. Thus there is no changed citation statement to substitute. The good-component result is now a split node, and its current statement explicitly supplies normal projectivity over F, the clopen inverse image and the finite restricted quotient. The tame quotient resolution remains a separate unsplit dependency. This delivery does not equate an unsplit dependency with a proved Lean theorem.

Under Review by Q109 above I retain the original source and step review. For this repair I reread ILO X 2.3 Step 2, diagram (2.c), and Step 3, printed pp.151--152, from the retained PDF extraction, and Stacks 01V6, morphisms.tex, lemma-smooth-characterize, including its final open-restriction assertion. In step 2 I now explicitly record the selected quotient's normal projectivity over F, exactly as the current good-component statement supplies. In step 4 I spell out descent of F through the invariant structure sheaf and the retained orbit-fibre and invariant-sheaf quotient properties, verifying that step 5 uses the same F-quotient. No new auxiliary theorem is used: these are the quotient hypotheses already given and the restricted quotient conclusion already cited in step 2. These edits keep the source route and every original hypothesis and conclusion.

I rechecked the repair against B--E. There is no new node to duplicate an existing theorem, hide a clause or lack searches. Step 1 uses finite-group Sylow existence; step 2 applies the identical model and quotient hypotheses; step 3 uses smooth restriction and the closed-embedding/SNC definitions on a clopen union; step 4 checks field scalars and group-order invertibility; step 5 uses finite separability and that exact finite geometric quotient; step 6 proves both support inclusions using surjectivity. Empty boundary, trivial group and nonfaithful actions still satisfy these checks. The longest non-elementary step is below 2000 characters. All original citations and logged searches are retained. The final dry run and push are performed after these edits; no unchanged re-push is being submitted.

## Unfinished work

None for this one-level split. The pre-existing tame quotient resolution remains its own downstream stage-1 item; this delivery introduces no additional downstream obligation.
