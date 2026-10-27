# Stage-1 report: lem-trf-affine-descent-saturation-quasi-affine-cover

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affine-descent-saturation-quasi-affine-cover.json: statement, split into six proof steps; no exact Mathlib match after four search kinds and a second semantic phrasing.
- citations.json: sixteen step/node pairs, quoting each cited statement verbatim.
- searches.jsonl: actual msearch output records, retained with the queries in the node.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All non-elementary inputs already have DAG nodes. The existing statement and statement dependencies are retained.

## Attachments

None. Searched the live project under lean/WeilConjectures for the exact blueprint tag, saturation with quasi-affineness, and descent/saturation notions. EffectiveDescent/Gluing.lean concerns already effective invariant opens, and CoordinateCoverDescent.lean concerns a different saturation defined by all fibres lying in an open. Neither proves this item's full statement. The existing open-restriction declaration is supporting material attached to its own node, not an attachment of this item.

## WANTED

None. All sources needed are present in literature/stacks-project/.

## Findings and corrections

The item is true as stated. There is no statement dispute. The imported node had no proof. In Stacks 02W8, the words "clearly" about quasi-compactness and containment conceal two short arguments: quasi-compactness of the base change followed by a continuous image, and normalization of the datum on the diagonal. Both are written out. The final covering is obtained from the affine basis and containment; it does not require quasi-compactness of V. The argument does not assume local finite presentation of the morphism V to A. Its local finite type follows from the Stacks locally quasi-finite hypothesis, not from the weaker Mathlib LocallyQuasiFinite class.

## Unfinished work

None at stage 1. Proof dependencies remain their existing nodes, with their existing statuses; no Lean was written and no compiler or build was run.

## Not duplicates

No new nodes were created. Whole-DAG searches and blueprint_refs searches for quasi-affine, quasi-finite and saturation found the existing quasi-affineness theorem, affine basis and local quasi-finiteness lemmas used here. The similarly named invariant-saturation sibling proves preservation by the descent relation, which is unnecessary for this item's clauses; it is not used and no cycle through the parent effectivity theorem is introduced.

## Review by Q156

I read Stacks more-morphisms.tex, Tag 02W8, label lemma-separated-locally-quasi-finite-morphisms-fppf-descend, particularly its second paragraph and the following covering conclusion. I also read morphisms.tex, Tag 01UA (lemma-fppf-open), the local quasi-finiteness definition 01TD and its finite-type remark; more-morphisms.tex, label lemma-quasi-finite-separated-quasi-affine; and schemes.tex, the affine-basis lemma 01IT, the quasi-compact affine criterion 01K4, and separated permanence 01KU. The chapter and unit records place this as the same supporting geometric descent chain below the local-term node; I did not change their route or records.

For step 1, I opened lem-weil-pbc-flat-lfp-open and verified that its statement includes openness after every base change, not merely the original map. The projection A times_B V to V is that base change. I opened lem-weil-pbc-open-immersion-base-change: it provides the open immersion C times_B A into V times_B A, so the image under the isomorphism is open before the open projection is applied. All hypotheses follow from p being flat and of finite presentation and C being open.

For step 2, I opened lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-morphism-permanence. Their statements respectively give quasi-compactness of C, preservation of a quasi-compact morphism under arbitrary base change, and quasi-compactness of its source when its target is quasi-compact. I use the projection to C, not the other projection. The finite-subcover argument then proves quasi-compactness of the image directly; no unmentioned image theorem or affineness theorem is needed.

For step 3, I opened def-pd-descent-datum and def-pc-fibre-product. The former states the full cocycle and invertibility, and the latter the pairing universal property. Pulling the cocycle to the small diagonal makes the diagonal transport idempotent; cancellation makes it the identity. Pairing a point of C with its structure map to A consequently puts that point in the saturation. This is an elementary consequence of those definitions, rather than a separate new normalization node.

For step 4, I opened def-weil-proper-morphism, def-weil-closed-immersion, def-weil-open-immersion and def-pc-fibre-product. The first defines separatedness by its closed diagonal, the next two give the actual sheaf and subspace definitions needed for the restriction argument, and the last gives the test-scheme identification of the restricted diagonal. Intersecting a closed image with an open is relatively closed, and restricting a surjective sheaf map stays surjective on stalks. Thus this few-line restriction argument is elementary from the definitions and does not hide a new permanence result.

For step 5, I opened lem-weil-pbc-lqf-restriction-to-opens and lem-weil-pbc-lqf-locally-finite-type. The former permits arbitrary source and target opens and therefore applies with target A itself; the latter explicitly uses the finite-type Stacks notion, as the item does. I opened the affine qcqs and qcqs-morphism nodes again: the already established quasi-compactness of W_C and quasi-separatedness of the affine target A are precisely their hypotheses for quasi-compactness of the restricted morphism. Finally I read the statement of lemma-nagata-quasi-affine-morphism-of-quasi-finite: all four hypotheses (separated, quasi-compact, locally quasi-finite, locally finite type) have now been established, and it concludes the relative quasi-affineness requested. These three non-Mathlib generic tools from other units are declared in split_report.tool_uses with the reason for each. I checked their dependency closures do not contain this item.

For step 6, I opened lem-weil-pbc-affine-opens-basis and verified its pointwise neighbourhood clause, not just an assertion of existence of some cover. Applying it to every point and then step 3 proves the covering. Empty V and empty affine C give empty images and vacuous assertions. With p the identity the diagonal-normalization argument gives W_C=C, as expected. Infinite disjoint unions of points over an affine base show why V must not be assumed quasi-compact; the proof never does. No argument needs V to be of finite presentation, and the separatedness argument never assumes an intersection of arbitrary affine opens is affine.

I checked delivery-errors B through E against the node and sources: no new unsplit-node proof text, duplicate, clause restatement, invented search, unintroduced object, route replacement, or uncited non-elementary claim was introduced. Every cited input has a verbatim quotation in citations.json. Each non-elementary step is shorter than 2000 characters. Searches returned generic affine-cover, quasi-compactness and locally-quasi-finite declarations; none encodes the saturation construction. The sole grep hit, QuasiAffine.lean:147, concerns preimages of the image of the canonical map to the spectrum of global sections, not a descent relation, so is not a match.
