# Worker report: lem-trf-fppf-finite-surjective-refinement

Group Q149, stage 1, 2026-10-18. This is a direct delivery with the worker's own review; no second worker or other agent was started. No Lean was written or compiled. The shared project and source checkouts were read only.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fppf-finite-surjective-refinement.json: item, statement, split; no Mathlib match for the full fppf refinement theorem. Its statement and statement dependencies are preserved.
- dag/nodes/sec-trace-formula/lem-trf-fppf-integral-surjective-refinement.json: new statement-only unsplit input, Stacks 0CNZ; no Mathlib match after LeanFinder (two formulations), Loogle, LeanSearch and grep. This is the only new node, with no new Mathlib leaves.
- report.md and citations.json: review and a verbatim statement quote for each node cited by each proof step. searches.jsonl contains the actual logged searches. The sandbox-only write_split.py is a preparation script, not a delivered project file.

## Attachments

None for the item. Search of WeilConjectures/ by the exact item id, fppf, integral refinement, and finite-surjective refinement found no declaration proving the full statement. EtaleFiniteRefinement.lean:70 states Scheme.exists_finite_surjective_refinement_of_etale only for a surjective etale map, so it cannot attach to this general fppf statement.

The existing closed node lem-weil-pbc-integral-morphism-limit-of-finite already records AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom, WeilConjectures/AlgebraicGeometry/Morphisms/Integral/FinitePresentationApproximation.lean:341; I read its statement and proof at lines 334-358 and reuse that existing node. No attachment edit is requested. There is no source declaration for the new 0CNZ input in the read-only slopmaster2 checkout.

## WANTED

None. The item's source and every new node's source are present in literature/stacks-project/.

## Findings and changes

The sandbox initially had only dispatcher markers. The repository item was unsplit, with an empty proof and no Lean audit identifying an existing implementation. I copied it and preserved its imported statement, source, ancestry, and earlier search evidence. The item agrees with Stacks Tag 0CP0, lemma-dominate-fppf-finite: qcqs base, arbitrary small fppf family, finite surjective finitely presented map, and open local lifts. No statement dispute or weakening was necessary.

The original source proof does not spell out two checks: why the descended opens cover, and why the selected finite-stage map is surjective. Step 5 supplies eventual equality of the finite union of the descended opens with the full stage, using the existing open-descent node. Step 7 proves surjectivity pointwise from q=p_lambda composed with pi_lambda. Surjectivity of the projection itself is never assumed. Step 4 checks quasi-separatedness of restricted stages; Step 6 does not impose quasi-compactness or quasi-separatedness on the fppf targets.

## Not duplicates

The new id was absent. Searches of the entire DAG for 0CNZ, lemma-dominate-fppf-integral, both orders of integral/surjective, and fppf refinement found no node giving this input. Whole-blueprint searches for fppf, integral surjective, integral morphism and dominate likewise found no equivalent blueprint node. No existing node has source tag 0CNZ, so there are no same-tag pairs requiring distinction.

lem-trf-fppf-integral-surjective-refinement vs lem-trf-fppf-finite-surjective-refinement: the new lemma allows any base scheme and constructs only an integral surjection, with no finite-presentation assertion; the item for a qcqs base must replace that potentially infinite object by a finite finitely presented one while retaining a covering and all local lifts. Steps 2-7 carry that finite-stage argument; it is not hidden in the new input.

lem-trf-fppf-integral-surjective-refinement vs lemma-weil-pbc-finite-refinement-etale-cover: the existing statement concerns an etale covering; it does not apply to arbitrary fppf morphisms. No second etale refinement node was created.

The existing limit input lem-weil-pbc-integral-morphism-limit-of-finite, open descent pqf-lem-limit-qc-open-descends, and locally-finitely-presented map factorization lem-weil-pbc-finite-presentation-map-limit-factorization were reused, together with the existing scheme permanence and affine-basis leaves.

## Review by Q149

I read more-morphisms.tex, the full statement and proof of lemma-dominate-fppf-finite (0CP0, lines 13757-13791), and lemma-dominate-fppf-integral (0CNZ, lines 13725-13755), including its two successive products and its restriction-to-an-open argument. I checked the tag-to-label map. The new node is exactly the integral-refinement assertion with all objects introduced; it is statement-only and has neither a proof sketch nor proof dependencies. It needs no qcqs hypothesis. Its notions have definition dependencies. It records real searches from this sandbox's log, including the second semantic wording; all services answered, and their returned definitions and descent-of-properties results do not provide the construction. The item also has a fresh recorded four-tool search, in addition to the preserved creation-time searches.

I read limits.tex lemma-integral-limit-finite-and-finite-presentation (09YZ, lines 1696-1722), all three clauses of lemma-descend-opens (01Z4, lines 553-570) and its proof, and all three equivalent conditions of proposition-characterize-locally-finite-presentation (01ZC, lines 1284-1311). Every cited node's actual statement was opened before drafting; citations.json quotes those statements verbatim, rather than inventing stronger versions.

Step 1 uses precisely the new 0CNZ statement: the given family is small, flat, locally finitely presented and jointly surjective, and the result gives both the integral surjection and the actual local factorization maps. This is a substantial input, not marked elementary.

Step 2 uses the definition of integral for affineness; affine-morphism-permanence (3) for quasi-compactness and quasi-separatedness; qcqs-morphism-permanence (2) to get a qcqs source over the given qcqs base; the affine-open-basis statement to refine the local lifts; the definition of quasi-compactness for a finite subcover; and affine-scheme-qcqs for the compactness of these affine opens. Restrictions of already constructed morphisms need no lemma. In particular, no arbitrary intersection of affine opens is claimed affine.

Step 3 takes the whole finite-presentation limit conclusion of the existing closed integral-morphism-limit-of-finite node. Its statement explicitly gives affine transitions, finite and finitely presented stages, and the factorization q=p_lambda pi_lambda. The same affine and qcqs permanence statements show that the stages meet the open-descent hypotheses.

Step 4 uses open descent (1) to descend each compact open, and its clause (3) for the restricted inverse-limit presentation, compact stages and affine transitions. Passing to a common stage preserves compactness by the cited quasi-compact-morphism-preimage-qc-open statement, whose quasi-compact morphism hypothesis follows from affine-morphism-permanence (3). I checked both directions of the quasi-separated-affine-cover criterion: any affine open of an open subscheme is also an affine open of the ambient stage, so its pairwise intersections are compact; the converse criterion then gives a quasi-separated open subscheme. This avoids assuming that the descended opens are affine without justification.

Step 5 uses exactly the eventual-equality clause (2) of the same open-descent node. The two opens are the finite union and the full compact stage; their inverse images coincide because the chosen V_j cover. The short finite-union compactness argument is written out. The node's statement does not itself contain a covering assertion; the step derives it from the clause it actually contains.

Step 6 uses fppf-site only for the locally-finitely-presented hypothesis, which that node's statement explicitly provides. Map-limit-factorization explicitly allows a locally finitely presented target over a fixed scheme S, with qcqs source stages and affine transitions. Here S=X and the stages are the restricted opens from Step 4. The resulting maps are X-morphisms. No separatedness of the targets, global finite presentation of the fppf maps, or descent of maps without finite presentation is used.

Step 7 is the elementary common-upper-bound and composition argument from Steps 3, 5 and 6, followed by a pointwise verification using the definition of surjective morphism. Step 8 treats the empty case by the identity and the empty open cover, writes its affine finite/presentation check, and uses the fppf joint-surjectivity clause to cover the possibility of an empty input family. The finite cover is small, under the retained universe convention. No step asserts that the new finite map is flat.

Small cases checked: the empty scheme with either an empty or nonempty fppf indexing family; a singleton identity cover (the identity suffices in both the input and output); and a field with a finite purely inseparable extension (finite flat fppf but not generally etale, so the found etale-only declaration is insufficient). The integral input also allows a non-quasi-compact base, so imposing compactness on it would have been an error. A finite stage need not have a surjective limit projection; the pointwise proof only needs the composite onto X. The proof handles a finite cover selected from an originally infinite family.

For delivery-errors B-E: the new statement is self-contained, sourced by a verified tag and label, with definition dependencies and exact logged searches. All substantial inputs are nodes whose statements give what is taken; no dependency uses an existing node's proof. There is one genuine intermediate theorem, not a copy of a clause of the item. Finite-stage construction, cover descent, and lift descent remain in the item's proof. No new step exceeds 2000 characters (the largest is 1014), no cycle is introduced by the new input (it has only definition dependencies), and no off-unit unsplit theorem or SGA source is used. The route follows the existing ancestor's Stacks-based ph/etale comparison; the unit and chapter records are untouched.

## Unfinished work

The new statement-only 0CNZ input is intentionally left unsplit for a later stage-1 worker. No required part of this item's proof remains implicit. The server dry run and direct delivery are run after this report is written; their terminal result determines the final response.
