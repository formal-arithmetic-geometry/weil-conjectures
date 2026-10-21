# Q63 stage-1 report: lem-sfb-etale-proetale-cube-flat-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-proetale-cube-flat-model.json: statement node, split into eight proof steps; Mathlib searches found no exact match or one-line specialization.
- citations.json: twelve step/node entries with verbatim statement excerpts.
- report.md: this report. searches.jsonl records the actual Q63 searches; prepare.py is sandbox-only preparation, not a delivery node.

New nodes: 0. Mathlib leaves: 0. The original item, citations, blueprint ancestry, source and previous Mathlib search records are retained. New Q63 searches were appended.

## Attachments

None. Searches in lean/WeilConjectures by the blueprint tag, K-flat terminology, and scalar/pullback comparison terminology found no project declaration stating this simultaneous six-face assertion. Generic K-flat and pro-etale derived operation declarations are only ingredients, not an attachment.

## WANTED

None. The relevant Stacks sources are present locally.

## Corrections and scope

The imported item had no proof. Its statement is unchanged. The statement is true for arbitrary discrete commutative rings and arbitrary scheme morphisms; no STATEMENT-DISPUTED correction is needed. The common-model argument uses ordinary uncompleted module sheaves, not completed integral coefficients or condensed coefficients. In particular scalar extension along a nonflat ring map need not preserve all quasi-isomorphisms, but it does preserve the resolving class in use, because it is a ringed pullback.

I retained the ancestor det-prop-scalar-six-direct-image and its two via nodes. The steps realize the formal-properties/finite-ring site-transport portion of that blueprint proof; they do not replace its later scalar projection formula or cohomological finiteness argument. Blueprint searches for K-flat, scalar/pullback and flat terms found no equivalent blueprint assertion (same_as remains empty). The item is not the unit's key statement, so no unit record is changed.

## Not duplicates

No new nodes were created. The general site resolution is already lem-pc-kflat-resolution (and the etale specialization is lem-kun-flat-resolution-existence). Preservation is already in lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Representative normalization for composition and specified geometric isomorphisms is already in lem-sfb-ringed-derived-composition-comparison and lem-sfb-ringed-derived-two-iso-comparison. Reusing these prevents duplicate nodes or moving the six-face assertion wholesale into a new lemma.

## Review by Q63

I read coord/delivery-errors.md B through E, the stage-1 brief and stage document, the three blueprint levels in SETUP.md, GOAL.md, the six-functors-basics chapter and scalar-six unit, and the ancestor's proof in main-20261015. For the item I read Stacks sites-cohomology.tex: Tag 06YS, lemma-K-flat-resolution; Tag 0G7E, lemma-pullback-K-flat; Tag 06YY, lemma-derived-base-change; Tag 0D6D, lemma-derived-pullback-composition; and Tag 07A4, lemma-pullback-tensor-product. These are the common-representative route, not an SGA route. I also read the complete statements of every cited DAG node, including the normalized comparison data definition referred to by the two composition/2-isomorphism nodes. There are no new-node sources to check.

Step 1 uses the general site resolution statement of lem-pc-kflat-resolution. Its hypotheses allow any sheaf of commutative rings and unbounded complexes, and its conclusion explicitly gives flat terms as well as K-flatness. It is stronger than what the item needs. I did not use lem-sfb-unbounded-kflat-resolution-existence, whose statement alone does not give flat terms and has additional categorical assumptions.

Step 2 uses the first, unconditional inverse-image-square assertion of sk-thm-pe-direct-image-comparison, not its qcqs direct-image assertion. The ringed pullback preservation clause of lem-weil-pbc-ringed-topoi-derived-tensor-pullback explicitly gives K-flatness AND flat terms. The identity geometric morphism with structural ring map A to B is a valid application, even when A to B is not flat. Iterating this statement verifies all suffixes as well as the six listed full vertices.

Step 3 uses the canonical natural representative counit of lem-weil-pbc-ringed-topoi-derived-pullback, the scalar derived construction of lem-pur-derived-change-of-rings, and the left-derived clause of lem-weil-pbc-exact-functor-derived-functor. The latter is essential for identifying the exact inverse images with the canonical left-derived presentations; an arbitrary objectwise isomorphism would not suffice. The recursive formula specifies the same identification at each shared vertex and avoids any new resolution choices. I checked the source and target rings at each of W0 through W5: each full word ends in B-module sheaves on X_proet, and each suffix has the ring needed by the next letter.

Step 4 uses precisely the statement of sk-thm-pe-direct-image-comparison that the ordinary exact square localizes to the unbounded derived square. I checked its two inputs separately: P at coefficient A, and the K-flat flat-term complex E_Y^e P at coefficient B. The latter is evaluated originally at T_Y^e QP, so the proof writes the naturality adjustment along its scalar counit rather than silently equating the two inputs.

Step 5 uses the representative formulas in lem-sfb-ringed-derived-composition-comparison and lem-sfb-ringed-derived-two-iso-comparison, together with the canonical composition comparison of lem-sfb-ringed-derived-monoidal-comparisons. The two paths have the same geometric inverse image and the same ring map: pulling a constant a then applying the coefficient map equals first applying it and pulling the resulting constant. Thus the specified geometric isomorphism is ring-compatible, exactly the hypothesis of the two-isomorphism node. The inverse direction for delta is recorded. The ordinary scalar insertion formula identifies these comparisons with the ordinary maps in the item; cancellation of the common representative yields their derived normalization. No use is made of the conclusion that the six faces commute; that belongs to the parent cube node, which this proof never cites.

Step 6 uses the defining representative equation of def-pur-etale-scalar-pullback-iso, whose statement explicitly supplies the specified etale map and its normalization for every K-flat P. I checked both orders of the two representative counits in that equation against the recursive j's. This deals with the actual chosen etale face, not just the existence of an etale scalar isomorphism.

Step 7 proves outer whiskering by writing the naturality square for the representative counit, whose naturality is explicit in lem-weil-pbc-ringed-topoi-derived-pullback. This is a short elementary consequence, so it is a proof step, not a new lemma node. It is applied separately to the scalar whisker of d_A and the geometric whiskers of delta_Y and c^e. The resulting list matches all six faces and their directions. Step 8 is induction on the same recursive j formula for a chain map P to P'; it uses the already established counit naturality. Neither step assumes that an arbitrary map between resolutions has an inverse as a chain map.

All twelve citations were generated with substring assertions against the complete current node statements; citations.json has one entry per use per step. The proof-dependency list is exactly their union. No proof step exceeds 2000 characters, and the elementary steps write the actual naturality calculation rather than hide a separate theorem. Off-unit generic tools are declared in split_report.tool_uses with their purpose; none replaces a unit step. The original statement dependencies remain exactly the notions the unchanged statement names.

Small cases checked: P=0; the empty scheme; A or B the zero ring; A=B and the identity coefficient map; f the identity; a nonflat quotient such as Z to F_p; and a genuinely unbounded flat-term K-flat resolution. The quotient example is consistent because scalar extension preserves flatness over the NEW ring and K-flatness, not flatness of B as an A-module. No boundedness, qcqs, finite-type, torsion, or coefficient-flatness hypothesis has entered. Constants and modules throughout are sheaves rather than a calculation only on global sections. There is no homogeneous interchange of factors, so no extra Koszul sign is present.

## Mathlib searches

I ran the prescribed Q63 msearch commands for leanfinder (two distinct phrasings), loogle, leansearch and grep. The grep of CategoryTheory found no K-flat representative counit. Loogle's SheafOfModules.pullbackComp and conjugateEquiv_pullbackComp_inv were read at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, lines 165–183: these compare ordinary module pullbacks, without this unbounded derived model assertion. The semantic hits concern ordinary pullback, free sheaves, site flatness or etale ring algebra. None gives this item, even by a one-line specialization. Exact queries and actual answers/digests are in searches.jsonl and appended mathlib_searches records. No unavailable service was recorded as absence.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own independent statuses; this delivery neither splits them nor claims their Lean proofs finished. Only stage 1 was performed, without any compiler, Lake, repository write, git command, or agent delegation.
