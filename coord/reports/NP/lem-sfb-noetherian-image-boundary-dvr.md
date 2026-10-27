# Stage-1 report: lem-sfb-noetherian-image-boundary-dvr

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-image-boundary-dvr.json`: item, statement unchanged, split into five steps following Stacks 0CM2 in affine coordinates. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-fg-field-dvr.json`: one new statement-only unsplit node, full algebraic Stacks 00PH; no Mathlib match. This is the only new node; zero Mathlib leaves are created.
- `citations.json`: 13 entries, one per proof-step/node pair, each quoting the cited statement verbatim.

## Attachments

No attachment for the item. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by closure, boundary, and DVR terminology found no declaration giving this diagram under these hypotheses.

`AlgebraicGeometry.exists_specializes_of_mem_closure_range` belongs to existing `lem-sc-picard-closure-specialization` (`lean/WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:70` in this snapshot). This is only the specialization input, not an attachment for the item. I did not edit that existing node. The already available `IsLocalRing.exists_isDiscreteValuationRing` in `RingTheory/DiscreteValuationRing/Dominating.lean:250` provides an injective local map but does not fix the fraction field or provide its required extension to the chosen source residue field, so it cannot replace the new 00PH node.

## WANTED

None. All proof sources needed are present in `literature/stacks-project/`.

## Findings and corrections

The imported item is correct as stated. Its restriction to points outside the image ensures the two primes in the affine target are distinct, and therefore ensures the local domain to which 00PH is applied is not a field. I kept every hypothesis and every conclusion. There was no existing split in the sandbox to recover.

I read Stacks `limits.tex`, label `lemma-reach-point-closure-Noetherian` (0CM2), including its proof, and its cited inputs `morphisms.tex`, label `lemma-reach-points-scheme-theoretic-image` (02JQ), and `algebra.tex`, label `lemma-exists-dvr` (00PH). The 0CM2 source also claims that the fraction field can be fixed to the residue field of a generic point of a component even when the selected specialization is trivial. That extra claim fails for the identity of Spec(k) when k is algebraic over a finite field: it would require a nonfield DVR with fraction field k, whereas every subring of such a field is itself a field (the inverse of each nonzero element is a power of it). The current boundary-only item already excludes this issue. There is no statement dispute in this delivery and no further statement correction is needed. My proof does not replace the source point by a generic component point: 00PH only needs its residue extension to be finitely generated.

I expanded the source's local-ring map as the explicit inclusion `(B/q)_(p/q) -> kappa(r)`. This makes the kernel, inverted denominators, fraction field, nonfield hypothesis, commutative diagram and special-point image independently checkable. No additional lemma is hidden in these computations. The new 00PH node is an algebraic existence theorem with arbitrary input local domain and field extension, not a renamed clause of the geometric item.

## Not duplicates

lem-sfb-local-domain-fg-field-dvr vs lem-sfb-local-domain-same-field-dvr: the existing 00PH specialization only constructs a DVR inside the unchanged fraction field K; the new statement prescribes any finitely generated extension L/K as the fraction field, which is needed for the source residue field.

lem-sfb-local-domain-fg-field-dvr vs lem-sfb-generic-dvr-properness-criterion: the existing node is a properness criterion for an integral scheme morphism; it mentions 00PH as a proof input and does not state the algebraic existence theorem, much less its field-extension version.

lem-sfb-local-domain-fg-field-dvr vs lemma-nagata-local-domain-valuation-dominates: the existing statement allows arbitrary field extensions and gives a valuation ring without discreteness. It cannot supply the DVR conclusion.

lem-sfb-local-domain-fg-field-dvr vs lemma-nagata-valuation-ring-extension: the existing statement extends an already given valuation ring by another valuation ring; it gives neither a DVR nor the Noetherian local-domain construction.

lem-sfb-local-domain-fg-field-dvr vs lem-sbc-noetherian-specialization-trait: the existing geometric statement traces a specialization but does not prescribe the fraction field as L or lift a selected field-valued source point.

I searched the whole DAG for 00PH, finitely generated field extensions, local-domain domination, residue-field finite generation, and image-closure specialization. Blueprint searches for `00PH`, `finitely generated field extension`, `dominat`, `discrete valuation`, `image boundary`, and `closure-specialization` found no blueprint node stating the new algebraic theorem or the item. The ancestor tool reports `blueprint.from.node = None` for this already-created chain. I retained the item's recorded null ancestor and explicit place, and prepended the item to the new node's inherited via chain.

## Review by NP

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the node files and the sources named above. The new node's full source is precisely 00PH, not the same-field specialization, and its statement introduces R, K, L, their embeddings, field generation, domination and fraction fields. No proof has been placed in its statement or proof fields. Definitions of Noetherian ring, field and DVR are cited, while local integral domain, fractions, finitely generated field extension and domination are defined inline. The item retains all its original statement definitions. JSON has single TeX escapes and no hollow definitions.

For step 1 I opened `lem-sc-picard-closure-specialization`, which states exactly that a point in the closure of the image of a quasi-compact morphism is a specialization of an image point. The finite-type definition supplies quasi-compactness and the affine finite-type charts. The local-Noetherian definition supplies a covering by affine spectra of Noetherian rings, so I choose a member of that covering; I do not need the stronger theorem that every affine open has Noetherian coordinate ring. Closure of a singleton proves that this chart also contains the general point. I declared the generic closure-specialization result as an off-unit tool rather than silently changing the unit route.

For step 2 I opened the spectrum, localization-at-prime and residue-field definition nodes. On the chosen affine charts the preimage prime q represents g(x). The closed set V(q) computes specialization, and the missing-image hypothesis implies q is strictly smaller than p. The quotient B/q embeds in L because q is the kernel; elements outside p are outside q, hence invertible in L. Thus the displayed fraction formula embeds R in L. The maximal ideal and fraction field identifications are the elementary localization and residue-field calculations recorded in the step; no field-extension lifting is being assumed here.

For step 3 I checked the Noetherian definition literally means every ideal is finitely generated. The proof explicitly lifts ideals through the quotient and contracts them through localization, proving the needed permanence in two ideal-generator calculations. It does not treat a theorem about Noetherian rings as supplied merely by a definition. A chosen b in p minus q stays nonzero in the domain's localization and is a nonunit, proving R is not a field. This verifies exactly the hypothesis that the unrestricted 0CM2 proof can overlook.

For step 4 I opened `lem-weil-pbc-finite-type-residue-field-extension-finitely-generated`. It applies to the finite-type ring homomorphism B -> C, not to a different or unstated notion of morphism, and its primes are r and its inverse image q. Its conclusion is finite generation of kappa(r) over kappa(q), which equals the fraction field of R from step 2. I then reread the new 00PH statement and the source: R is a Noetherian local domain, R is not a field, and L/K is finitely generated. All four requirements hold before invoking it. It supplies both the prescribed fraction field L and contraction of the maximal ideal; the same-field node would not suffice.

For step 5 I opened again the spectrum, residue-field and localization nodes. These define the actual maps C -> L and B -> R -> A. Commutativity is checked by equality of the maps on every b in B. The special-point condition follows by two explicit contractions of the maximal ideal, ending at p. This uses the actual domination conclusion of 00PH and does not infer scheme factorization merely from containment of point images. The field in the item's conclusion is L, a permitted renaming of its existentially bound K.

For small cases, the empty source and a point already in the image give no boundary input. For `Spec(k[t,t^-1]) -> Spec(k[t])` at (t), q=0, p=(t), R=k[t]_(t) and L=k(t), recovering the usual trait. With source `Spec(k[t,t^-1,z])`, L=k(t,z), so the field-extension clause of 00PH is essential. A nilpotent thickening in B is removed by the prime quotient before using a domain. A singular example B=k[s^2,s^3], q=0, p=(s^2,s^3) is allowed: no normality, excellence or regularity is assumed. For the new 00PH node, L=K recovers the existing same-field statement; R already a DVR works; transcendental and inseparable finite extensions are included by the source's unrestricted finitely generated extension hypothesis. The excluded field case is necessary, as the algebraic-over-finite-field example shows.

I read all Mathlib search hits and their relevant source interfaces. Searches used only the required msearch.py command and are logged verbatim. Both semantic phrasings returned DVR characterizations or ordinary valuation extension interfaces, not this existence theorem. In particular `Valuation.HasExtension` is a compatibility hypothesis on given valuations; it is not an existence theorem. The item searches likewise returned the general valuative criterion (requiring a lifting assumption) and generalizations through a stalk, neither of which supplies this diagram. One exploratory grep mistakenly named `Valuation/Extend.lean`; its empty result was not used as absence evidence or recorded in a node. The corrected file `Valuation/Extension.lean` was read and searched. No service failure was reported as absence.

All five proof steps are under 1000 characters, so no step exceeds the long-step threshold. I checked that each quoted citation is an exact substring of its node's statement and that proof_deps equals the union of step uses. The only new dependency is strictly algebraic and cannot depend on the geometric item. No SGA source is used. No Lean was written or compiled, and the read clone and launcher files were untouched.

## Unfinished work

Only the new statement-only 00PH node remains to be split in a future stage-1 item, as required by one-level splitting. Nothing in this item's split is left unproved except the explicitly cited nodes.

## Validation

The server dry run passed preflight, DAG and split checks. I corrected the report-only line reference for the existing specialization declaration from 74 to 70 after reading the exact declaration line, then reran the final dry run before pushing.
