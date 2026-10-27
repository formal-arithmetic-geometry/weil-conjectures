# Stage-1 worker report: lem-sfb-proopen-global-section-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proopen-global-section-extension.json: split statement, six proof steps; no Mathlib match for the full statement.
- citations.json: a verbatim statement quote for every node cited by each numbered proof step.
- searches.jsonl: actual msearch.py searches, retained verbatim.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing nodes already supply every non-elementary ingredient. The sandbox initially contained only dispatcher marker files, with no earlier item, report or search log to continue.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, proopen/pro-open, flat monomorphism, ringed image/subspace and neighbourhood section extension. No project declaration states the item. The compactification graph proof uses a flat monomorphism with finite-presentation hypotheses to obtain an open immersion and is not an attachment.

## WANTED

WANTED: Michel Raynaud, Un critère d’effectivité de descente, Séminaire Samuel 1967–1968, exposé 5, Propositions 1.1 and 1.2(i), printed pp.1–2, Lemma 2.2 and Proposition 2.3(i), printed pp.4–5, for lem-sfb-proopen-global-section-extension and the existing lem-sfb-qc-flat-monomorphism-ringed-image. Expected archive literature/raynaud-critere-effectivite-descente.pdf is absent. I read the primary Numdam scan https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf online without writing into literature or downloading a private archive. The proof_origin is agent, as required while the local source is missing, with the exact available Stacks source for the closure argument.

## What was wrong or needed completion

The imported item was unsplit, not false: its proof was empty. Its statement and hypotheses have been retained verbatim. In particular no local finite presentation, Noetherian hypothesis, affineness of overlaps, or separatedness has been added. The existing ringed-image node is broader than the present use: I use its canonical ringed-space identification, generalization stability and retrocompactness, not its factorization clause.

The nearest-ancestor command returns None. The existing blueprint.from.node is null and its long inherited via chain leads through created prerequisites rather than an imported ancestor. I preserved that metadata, filled same_as after whole-blueprint searches, and explained the inherited place in split_report.blueprint. This item is not its unit's key node, so no unit realization fields were changed. I read the chapter and unit records and the current latest blueprint (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), including the direct-images statement/proof. This prerequisite serves the existing deeper Raynaud/trait descent branch; it changes no chapter or unit route.

## Mathlib searches and near hits

The item's earlier recorded Q28 searches were preserved. I also ran the required msearch.py semantic, Loogle and source searches under N9 and read their actual hits. The two semantic phrasings were the global regular function extension statement and extension of inverse-image sections from a quasi-compact generalization-stable retrocompact subset. LeanSearch queried neighbourhood colimits of pro-open sections. Loogle queried Flat and Mono; grep used the flat/mono, pro-open and neighbourhood-section patterns in AlgebraicGeometry. No service failure was recorded as a no-match.

I read Mathlib/AlgebraicGeometry/Morphisms/FlatMono.lean lines 25–50: Flat.isIso_of_surjective_of_mono additionally requires surjectivity, and IsOpenImmersion.of_flat_of_mono at line 38 requires LocallyOfFinitePresentation. I read Morphisms/QuasiSeparated.lean lines 318–332 and 398–428: exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated, isLocalization_basicOpen_of_qcqs and exists_of_res_eq_of_qcqs extend sections from a principal open after powers of a denominator; they do not extend from the arbitrary flat monomorphism here. AffineTransitionLimit.lean lines 824–843 shows exists_appTop_π_eq_of_isAffine_of_isLimit assumes an actual affine limit diagram, absent from this item. These are not one-line specializations. Scheme.Opens.toScheme_presheaf_obj only identifies restriction values. I therefore retained status split rather than mathlib.

## Not duplicates

No new node was created. Existing lem-sfb-qc-flat-monomorphism-ringed-image supplies Raynaud 1.2(i); lem-per-flat-monomorphism-local-structure supplies only local ring/fibre properties and is unnecessary. Existing lem-sfb-generalizing-subset-affine-envelope concerns a canonical affine envelope and is neither needed nor an extension theorem. I did not cite the parent lem-sfb-flat-monomorphism-quasiaffine-neighbourhood, which already depends on this item and would create a cycle. The general spectral closure lemma is reused rather than creating a separate constructible-avoidance lemma. Searches of all DAG statements/titles, source places and the whole imported blueprint found no synonymous blueprint statement (flat monomorphism, ringed subspace, ringed image, proopen and regular function searches).

## Review by N9

I checked sections B–E of delivery-errors.md against the written node and the actual cited statements, not their proofs. There are no new statements to audit. The sources I read for the item were Raynaud's primary scan, especially pp.1–2 and 4–5, and the available Stacks text: topology.tex lemma-constructible-stable-specialization-closed (Tag 0903), properties.tex lemma-quasi-compact-quasi-separated-spectral (Tag 094L), schemes.tex lemma-basis-affine-opens (Tag 01IT), and sheaves.tex lemma-stalk-pullback (Tag 008H). Raynaud's two-open gluing proof removes a constructible bad set; I made the avoidance explicit by taking its closure and using the already-existing 0903 statement. This is the same finite-gluing route, written simultaneously for the finitely many pairs. It does not use SGA.

Step 1 cites lem-sfb-qc-flat-monomorphism-ringed-image. I opened its statement: it explicitly identifies the source with the induced ringed subspace and states both generalization stability and retrocompactness with no separation or Noetherian hypothesis. Its quasi-compact flat monomorphism hypotheses are exactly available. Compactness of E follows from the supplied homeomorphism and compactness of Z, by pulling back any open cover.

Step 2 uses lem-weil-pbc-topological-inverse-image-stalk for its explicit representative and unit/germ formula, def-weil-pbc-module-stalk for the equal-germs iff equality on a neighbourhood clause, lem-weil-pbc-affine-opens-basis to refine that neighbourhood, and lem-weil-pbc-qcqs-scheme-spectral for spectrality. I verified that the inverse image here is the ordinary topological ring-sheaf inverse image, not an étale or scalar-extension pullback. A neighbourhood open in E is the trace of an ambient open, so refining inside its intersection with N_e makes the induced section agree on the entire trace E cap U_e. The finite cover comes from compactness of E. U_0 is a finite union of affine opens, hence compact; quasi-separatedness is inherited from Y. I apply spectrality to U_0, never to the possibly noncompact Y.

Step 3 cites pqf-lem-qs-intersection-qc for compactness of A_ab, the ringed-image node for retrocompactness of E, and the same inverse-image-stalk, stalk-definition and affine-basis nodes. Each cited statement says precisely what is used. Retrocompactness applies to A_ab because that is a compact open in Y; therefore E cap A_ab has a finite cover by equality neighbourhoods. The inverse-image stalk isomorphism is injective, which is needed to transfer equality back to O_{Y,e}. Locality of the structure sheaf makes the two sections equal on the union W_ab. I did not assume intersections of affines are affine.

Step 4 uses lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact and def-weil-constructible-subset, whose statements explicitly identify compact opens with retrocompact opens on the spectral space and allow differences and finite unions. The bad sets F_ab are constructible in U_0, not claimed closed there. The step is elementary application of those exact statements.

Step 5 uses lem-weil-pbc-spectral-proconstructible-closure-specialization, the ringed-image generalization-stability clause, and the affine basis. The closure lemma accepts an intersection of constructibles; taking a singleton family gives precisely the constructible F at hand. If e lies in its closure, it is the specialization of f in F, so f is a generalization of e. Stability of E puts f in E and contradicts avoidance. I checked this direction explicitly: the opposite specialization direction would be invalid. Removing closure(F) produces an actual open neighbourhood of all E; another finite affine selection yields a compact V without claiming that this whole open is compact.

Step 6 uses lem-weil-pbc-morphism-factors-through-open-subscheme, whose statement supplies a scheme factorization from containment in an open, and def-weil-locally-ringed-space-morphism for the sectionwise structural map. The remainder is exactly the defining sheaf gluing/uniqueness axiom: every overlap in V avoids its F_ab and is contained in W_ab, so the specified restrictions agree. On the covering j^{-1}(U_a) the pullback equals s by the original canonical ringed-image identification and the representative construction. Equality is local on that covering, giving the required global equality. This step does not assert factorization through an arbitrary locally closed subset.

I listed generic tools of other units in split_report.tool_uses, with individual reasons; no top-level maintainer-owned tool_uses field was set. citations.json quotes the full statement of each node for each step so all used clauses and hypotheses are reviewable. All six steps are below 2000 characters, with no subclaim hidden by a “standard” or “transport” assertion. The only topology consequence proved inline beyond gluing is a short direct application of the existing closure theorem; it would be an elementary duplicate to create a new avoidance node.

Edge cases: when Z (hence E) is empty, the empty open and its unique section suffice, stated in step 1. Empty pairwise E-intersections use W_ab empty. A one-chart cover has no gluing obstruction. A surjective j gives E=Y, and the ringed-image theorem identifies j with an isomorphism, consistent with taking V=Y (which is then compact). For Spec S^{-1}A into Spec A, a section has a denominator from S and extends on its principal open; the proof does not assume this localization description in general. Nonseparated quasi-separated Y is allowed throughout. Nilpotents cause no loss because agreement is of germs/sections of rings, not just pointwise residue values. No statement dispute was found.

## What could not be finished

Final citation correction: I added lem-weil-pbc-affine-scheme-qcqs to steps 2, 3 and 5 after reading its explicit quasi-compactness clause. This supplies compactness of every affine neighbourhood before taking a finite union; it is not inferred solely from the affine-basis statement. Its source is Stacks Tag 00E8, algebra.tex lemma-quasi-compact, with Tags 01KN/01KO for the unused quasi-separatedness clause.

The preliminary server review_split passed with zero new nodes, and the first full dry run exited successfully at 5fc70b152bb. A final dry run follows the citation correction.

Nothing in the stage-1 split is left unfinished. The local Raynaud archive remains WANTED. Validation and direct delivery results are recorded below once the required server tools finish.
