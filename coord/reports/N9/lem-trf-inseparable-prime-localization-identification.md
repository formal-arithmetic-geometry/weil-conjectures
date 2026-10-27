# Worker report: lem-trf-inseparable-prime-localization-identification

## Files written

- dag/nodes/sec-trace-formula/lem-trf-inseparable-prime-localization-identification.json: existing statement, split into six steps. Not a Mathlib leaf as a whole. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the eleven step/node citations.
- searches.jsonl: actual msearch records; the item's inherited searches are retained and today's searches appended to mathlib_searches.
- report.md: this report.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for prime-localization and purely inseparable base-change notions. Algebra.TensorProduct.purelyInseparable_baseChange_localRing in RingTheory/PurelyInseparableBaseChangeLocalRing.lean assumes IsNoetherianRing A and does not assert this prime-localization isomorphism or its compatibilities. Its existence therefore does not attach this item. Mathlib's spectrum homeomorphism is only an ingredient, already available through an existing more general scheme node.

## Literature wanted

None.

## Corrections and scope

The statement is unchanged. The item was statement-only; it needed an actual argument for the inverse-image prime, inversion of all denominators outside that prime, and the structural and universal compatibility clauses. I supplied these, rather than citing the Noetherian theorem under hypotheses that are not available. No imported blueprint field or maintainer-owned field was changed. The existing blueprint.from.place already specifies the inherited geometric-point descent branch and has been retained.

The chapter and sk-i-curve-zero unit were read. This is a generic algebra input in the inherited geometric-reducedness descent branch, not the unit's key statement. No unit realization or route change is made. I also read the current ancestor's blueprint_update; none of its newer contracting-correspondence assertions is replaced or restated here.

## Unfinished work

None in this one-level split. All proof inputs already exist in the DAG. No Lean is written or compiled.

## Not duplicates

There are no new nodes. Searches of the whole DAG and blueprint found the existing more general lem-pc-homeo-pure-insep, the affine fibre-product lemma, and the needed localization and local-ring lemmas. I cite those directly rather than create affine special cases or new nodes for clauses of the item. The item is not the same statement as lem-pc-homeo-pure-insep: it also identifies the actual localized rings and fixes every structural and universal map.

## Review by N9

I read Stacks varieties.tex Tag 035W (lemma-geometrically-reduced-at-point), especially its first proof paragraph, and algebra.tex Tag 0BRA (lemma-p-ring-map). The latter supplies the unchanged spectrum after purely inseparable extension; 035W uses this to identify a unique local ring. I expanded the ring comparison from the actual fraction formulas of algebra.tex Tag 00CP (proposition-universal-property-localization). I also read Tag 00E9 (lemma-characterize-local-ring) and the tensor-localization argument Tag 00DK (lemma-tensor-localization). No new node needs an additional source. There is no SGA citation in this split.

For step 1 I opened lem-pc-homeo-pure-insep, lem-weil-pbc-fibre-product-affine-spectra, and def-weil-affine-spectrum. Their statements respectively give the homeomorphism for an arbitrary scheme over a field, its affine tensor-product model with both projection maps, and the prime-ideal spectrum with its Zariski topology. Hence they apply to both Spec A and Spec R with no finite-type or Noetherian restriction. The specialization-order argument is explicitly written via closure{Q}=V(Q); it supplies both directions of inclusion, not merely a continuous bijection. The scheme homeomorphism is a generic off-unit tool, declared in split_report.tool_uses; it is also recorded Lean-closed in the live node.

For step 2 I read def-weil-pbc-localization-at-prime and lem-weil-pbc-proper-ideal-contained-in-maximal. The former explicitly includes locality of R_p and its maximal ideal; the latter gives maximal-ideal existence above each proper ideal. I use these statements, not merely a definition of locality or an unstated existence principle. The maximal-implies-prime argument is written in the step. The order correspondence makes the prime above m greatest among primes, and the existence lemma then makes it maximal and the unique maximal ideal. This does not assume that all primes of A or C are maximal.

For step 3 I read the entire statement of lem-weil-pbc-localization-tensor-over-base, checking its independent base ring and algebra parameters. Substituting base k, algebra R, module R, multiplicative set R minus p, and second module E gives precisely R_p tensor_k E as a module localization of R tensor_k E. I explicitly check multiplication and 1 to turn the module comparison into a ring comparison, and spell out units, fraction representation, and kernel annihilation. The ring universal property is taken from lem-weil-pbc-ring-localization-universal-property, whose statement I opened; the category-localization node with the similar name is not used. This avoids silently treating a module isomorphism as a ring isomorphism.

For step 4 I read lem-trf-localization-maximal-contraction. It says exactly that the maximal ideal of R_p contracts to p. Together with step 2, inverse-image primality, and uniqueness over p from step 1 applied to R, this proves j^{-1}(n)=P for the actual map j. No general localization prime-correspondence theorem is smuggled in here.

For step 5 I opened lem-weil-pbc-local-ring-unit-criterion and checked its exact hypothesis: C is local by step 2, so an element outside n is a unit. The inverse-image equality from step 4 therefore inverts every required denominator. The previously quoted ring universal property gives theta and its formula. Step 3 gives the reverse map because contraction of P is p. I check each composite on S and use uniqueness for its particular localization; the argument proves an isomorphism, not just a map or a bijection of primes.

For step 6 the same universal-property node explicitly includes the fraction formula and equality of maps agreeing on the original ring. On A I check the element r/v, whose image is (r tensor 1)/(v tensor 1). For an arbitrary map to D inverting S minus P, the images of V are among those units, so both factor maps exist and agree by uniqueness. No locality or injectivity condition on D is introduced.

I checked delivery-errors B through E against these files. Each use is a node statement, copied verbatim into citations.json; no new unsplit proof, duplicate node, or circular dependency is introduced. I traversed the cited nodes' existing dependencies and none reaches this item. Every step is shorter than 2000 characters. Steps 4 and 6 are elementary assembly of earlier results and the explicitly cited maps; the substantive homeomorphism, maximal-ideal existence, tensor localization, unit criterion and universal property are all cited. I retained all old search records; today's actual semantic, Loogle and grep searches were read and logged, with a second phrasing. The spectrum theorem is Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean:65; its type lacks the localization and compatibility conclusions, so it is not a match for the full item.

Small cases checked: E=k makes theta the ordinary localization identification, and characteristic zero reduces to that case because purely inseparable extensions are trivial. Taking R=k[epsilon]/(epsilon^2) shows why no reducedness is inferred. Taking a nonclosed prime of a polynomial algebra tests the general-prime wording; a polynomial algebra in infinitely many variables tests the absence of Noetherianity. The proof uses neither finite generation of R nor closedness of p, and in fact the argument works without the stated finiteness of E/k. The zero ring has no prime p and so supplies no missing exceptional case. A map to the zero ring D satisfies the universal conclusion as well. No hypothesis or conclusion has been weakened.
