# Q75: lem-sfb-decent-space-finite-field-map

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-decent-space-finite-field-map.json: item, split; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-quasicompact-monomorphic-points.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-closed-point-field-immersion.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation per step/node citation.

## Attachments

None. Searched WeilConjectures for the blueprint tag, decent, algebraic-space and field/quasi-compact terminology. No project declaration states the item. Scheme-only residue-field declarations do not suffice.

## WANTED

None.

## Corrections and route

No statement dispute or change. The item is precisely the finite-morphism assertion of Stacks 08AL; its additional closed-immersion clause is not part of this item. The proof previously was empty. The two decency formulations in neighbouring nodes need an actual theorem before applying the existing closed-image node; its hypotheses cannot simply be identified by a prose synonym. Tag 03JV supplies that theorem.

Read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability direct-images proof and its section; this is a supporting algebraic-space tool deep below its direct-image prerequisite, not a replacement of the unit route. The existing ancestry resolves to null with the long inherited via chain; preserved that provenance and filled the new nodes' precise Stacks roles. Blueprint searches for decent, quasi-compact monomorphism, reduced closed and closed point found no blueprint statement of the two new lemmas. The whole DAG was searched for those terms and tags 03JV and 0AHB, and the current project Lean source was searched before writing either node.

The finite scheme-morphism facts and point-class definition are generic tools from other units; split_report.tool_uses declares these uses. No finite-morphism calculus for spaces is silently assumed: step 5 works exclusively with finite scheme tests.

## Review by Q75

I read decent-spaces.tex Tag 08AL (lemma-finite-residue-field-extension-finite), its proof, Tag 03JV (lemma-UR-finite-above-x), the definition 03I8 and the entire proof of 0AHB (lemma-decent-space-closed-point). For the first new node, 03JV explicitly lists all-field-map quasi-compactness as condition (6), and existence of a quasi-compact monomorphic representative as (4); it holds pointwise without diagonal quasi-compactness. For the second new node, 0AHB explicitly gives a closed immersion from a field spectrum at every closed point of a decent space. This is a strict supporting result: it assumes a point already known closed, and says nothing about finiteness of an arbitrary finite residue extension over a base. It can later be split by the atlas proof printed at 0AHB, which uses finite etale field fibres and target-locality of closed immersions. Both new nodes contain statements only.

Step 1 uses the first new node to meet exactly the monomorphic-representative hypothesis of lem-sfb-decent-algebraic-field-image-closed. I opened that existing node and checked it needs only algebraicity of the given L/kappa(s) and closedness of s, with no finite-type hypothesis. Linear dependence of powers proves algebraicity here. Step 2 uses exactly the field closed immersion asserted by the second new node; it does not take a residual field construction from the proof of another node.

Step 3 uses the second node's scheme-test closed immersion, the common-field-extension equivalence in def-a1-algebraic-space-point-classes, and the quotient-on-affines description in def-weil-closed-immersion. I checked their statements. A common representative makes the pullback nonempty; the quotient ideal in a field is then zero. This explicitly proves factorization, without assuming that topological containment alone suffices for arbitrary nonreduced sources.

Step 4 uses the compatible field homomorphisms of def-weil-residue-field on the actual scheme composite Spec L -> Spec K -> S, not an undefined residue field for a general algebraic space. Its image is s because both maps factor a. The inclusions are injective because they are unital maps of fields. An original finite spanning set over kappa(s) still spans over K. The exact statement of lem-weil-pbc-spec-finite-ring-map-finite then makes Spec L -> Spec K finite.

Step 5 uses the scheme-test assertion of the second node to construct W, the scheme fibre-product universal property in def-pc-fibre-product for V, the finite base-change clause of lem-trf-finite-radicial-basechange, the scheme closed-immersion-finite assertion of lem-weil-pbc-closed-immersion-finite, and the scheme finite-composition assertion of lem-weil-pbc-finite-composition. I opened all these statements and checked each is applied to schemes; the radicial clause is unused. Consequently V is a representing scheme, and its finite composite to every T proves precisely both requested clauses.

Small cases checked: the empty space makes the existence of a vacuous; empty tests give empty finite maps; degree-one extensions yield the closed field subspace, consistently with 08AL. Purely inseparable finite extensions are allowed throughout. S, X and T need not be Noetherian, separated or of finite type, and T can be nonreduced. The field-source argument in step 3 uses reducedness only through the field having no nonzero proper ideal. The new closed-point lemma allows a nonreduced ambient space. The point-representative lemma is vacuous for empty X and has no relative-diagonal assumption. No step exceeds 2000 characters.

For delivery-errors B, I checked self-contained objects, notion dependencies, single TeX escapes, precise tags and labels, statement-only new nodes, search logging, and blueprint metadata. For C, every non-elementary fact has a cited statement, with no use of a cited proof; citations.json quotes those statements verbatim. For D, the new nodes are supporting lemmas, not restatements of the arbitrary L/base-point conclusion; the assembly contains the field factorization and all finite-map reasoning. For E, the hypotheses and scheme/space distinctions above were checked against each source. No SGA reference or compiler was used.

Mathlib searches are recorded from searches.jsonl. LeanSearch and LeanFinder returned scheme-only residue or quasi-compactness statements; Loogle returned no hits for algebraic-space combinations; the grep hit is an unrelated English word in Ordset.lean. A second natural-language formulation was tried for each prospective lemma. In particular Mathlib's isClosed_singleton_iff_isClosedImmersion (Morphisms/ClosedImmersion.lean:423, read at lines 423-428) quantifies over schemes and does not discharge the closed-point lemma for spaces.

## Not duplicates

lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-qs-space-field-monomorphism: the existing statement assumes a quasi-compact relative diagonal; the new statement assumes only quasi-compact field-valued maps.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-qs-space-rational-point-topology: the existing statement concerns injectivity and closedness of rational points over a field under a quasi-compact diagonal, not monomorphic representatives in a general decent space.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-decent-algebraic-field-image-closed: the existing statement assumes monomorphic representatives to prove closedness of a particular algebraic field-valued image; the new node establishes those representatives.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-relative-qs-affine-chart-point-fibres: the existing statement bounds atlas fibres under a quasi-compact diagonal; it does not construct representatives under decency alone.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-quasiseparated-space-etale-specializations: the existing statement lifts specializations under a quasi-compact diagonal; it does not give the decency characterization.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-locally-separated-space-decent: the existing statement derives decency from an immersive absolute diagonal, whereas the new statement relates field-point conditions without that hypothesis.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-locally-separated-rational-point-closed-immersion: the existing statement concerns rational sections over a field under local separatedness, not monomorphic representatives of every point of a decent space.
lem-sfb-decent-quasicompact-monomorphic-points vs lem-sfb-decent-space-finite-field-map: the item concerns finiteness of a specified field-valued morphism over a closed base point with finite residue extension; the new node concerns representative existence at every point without either base-point hypothesis.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-decent-space-finite-field-map: the new node constructs a field representative for a closed point already given; the item proves finiteness of a specified map whose image is not initially known closed and whose source field can be larger.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-locally-separated-rational-point-closed-immersion: the latter requires local separatedness and a rational section over a field; the new node uses decency and closedness and merely constructs a representative over a general scheme base.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-space-reduced-closed-support: the existing node constructs a reduced closed algebraic subspace, not a field spectrum representing a closed point.

## Unfinished

The two new statement-only lemmas join the stage-1 queue. The assigned item's split is complete.

## Not duplicates

lem-sfb-decent-closed-point-field-immersion vs lem-sfb-decent-algebraic-field-image-closed: the existing result proves topological closedness of an image over a closed base point with algebraic residue extension; the new result constructs a representable closed immersion from a field once a closed point is already given.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-locally-separated-space-decent: the existing result proves decency from local separatedness and has no assertion constructing a closed field subspace.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-qs-space-field-monomorphism: the existing result constructs a quasi-compact monomorphism assuming a quasi-compact diagonal, but neither a closed immersion nor the weaker decency-only hypothesis.
lem-sfb-decent-closed-point-field-immersion vs lem-sfb-relative-qs-affine-chart-point-fibres: the existing result bounds atlas fibres under a quasi-compact diagonal, without constructing a closed field representative of a closed point.
