1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-affine-basechange.json` (repaired split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generator-exists.json` (statement-only; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generator-pullback.json` (statement-only; no Mathlib match).
- `dag/nodes/sec-picard-framework/def-sc-duality-equation-base-change-map.json` (definition; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-sc-flat-precompose-pus.json` (statement-only; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-affine-morphism-hom-out-of-perfect.json` (statement-only; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-global-hom-adjunction.json` (statement-only; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-base-change-rhom-perfect.json` (statement-only; no Mathlib match).
- `citations.json`.

2. Attachments: none.

3. WANTED: none. The Stacks corpus was read from `/home/ubuntu/c1-stacks-review/`.

4. The return identified five defects. I deleted the bundled `lem-sc-affine-perfect-generator-rhom-basechange`, since it restated the item, and deleted `lem-sc-flat-tor-independence-affine`, since its affine tensor sentence was only flatness rather than Stacks Tor independence. Step 1 now states Tor independence correctly at stalks and treats the affine tensor calculation as elementary; it cites the new definition of the mate-defined canonical map. The RHom comparison is split across the existing Tag 0A1H node `lem-pc-proper-support-perfect-direct-image` and four separate inputs: affine Hom-out-of-perfect, global RHom adjunction, algebraic perfect RHom base change, and the compatibility of the comparison with the mate. The two generator gaps are covered by separate nodes for existence of one perfect generator and for affine pullback of a generator. The report no longer claims a source reading that was not performed or cites the direct-image node as an unused check.

## Review by K1

I checked the item against Tag 0AA8 (Lemma 48.6.2), case (1), in `/home/ubuntu/c1-stacks-review/duality.tex`, and against its parent `lem-sc-proper-flat-right-adjoint-basechange`. The item hypotheses remain affine Y and Y', proper flat finitely presented f, the cartesian X', and right adjoints on D_QCoh; the added definition node supplies the canonical map named by the conclusion. The source file and cited clauses were read directly from the imported Stacks corpus.

Step 1 uses only the mate-map definition; flatness gives the stated Tor vanishing at stalks, and the affine derived-tensor calculation is a two-line consequence of flatness. Step 2 uses the new single-generator statement, the new affine-pullback generator statement, and the existing `lem-pc-proper-support-perfect-direct-image`; the latter says perfect direct image and arbitrary base change, and specializes with E=O_X and M in degree zero. Step 3 uses the new mate-compatibility statement, affine Hom-out-of-perfect base change, global RHom adjunction, the Tag 0A1H direct-image/base-change statement, and algebraic RHom base change; each cited statement contains the exact comparison used. Step 4 uses the pulled-back-generator statement and the map definition to conclude by generator detection.

For every new node I searched the DAG and blueprint by its key terms before writing it, then ran LeanFinder, Loogle, and Mathlib grep searches. The searches found only generic category-theory mates, affine morphism, or flatness declarations, not these scheme-level statements. All new nodes are statement-only except the map definition, introduce their objects and hypotheses, carry the nearest blueprint ancestor `lem-sc-finite-duality`, and have no proof dependencies. Small checks used in reviewing the split were the identity affine map, a field base change, and the zero perfect complex as a non-generator (which is excluded by the generator hypotheses). The repaired split specifically addresses the prior D1/D2 bundled conclusion, C4 missing generator and map statements, C1 missing RHom inputs, and the incorrect Tor node.

5. The returned defects were repaired: the base-change map is the explicit three-arrow composite with the Tor-independent middle arrow inverted; the flat-precompose node states the conjugate isomorphism and RHom compatibility; the affine RHom node uses the cartesian affine-base Tor-independent statement; global RHom and qcqs right-adjoint existence are stated separately; and the perfect direct-image specialization uses E=M and G=O_X[0].

## Not duplicates

`def-pc-global-derived-rhom` vs `lem-sc-proper-flat-right-adjoint-affine-basechange`: the new definition introduces the global RHom construction, while the item asserts an isomorphism of right-adjoint base-change maps.
`lem-pc-perfect-generator-exists` vs `lem-pc-perfect-generation-open-induction-step`: the new node asserts existence of one perfect generator for every qcqs scheme; the existing node is an induction step for generation by perfect complexes.
`lem-pc-perfect-generator-exists` vs `lem-pc-perfect-generation-affine-base`: the new node asserts a single generator; the existing node treats the affine-base generation argument and does not state single-generator existence.
`lem-pc-perfect-generator-pullback` vs `lem-pc-perfect-generation-open-induction-step`: the new node asserts affine pullback preserves a chosen generator; the existing node is an open induction step.
`lem-pc-perfect-generator-pullback` vs `lem-pc-perfect-generation-affine-base`: the new node concerns pullback of a generator; the existing node concerns generation on an affine base.
`lem-pc-qcqs-derived-direct-image-right-adjoint` vs `lem-pc-noetherian-derived-direct-image-right-adjoint`: the new node is the qcqs theorem from Tag 0A9E; the existing node is a Noetherian specialization.
`lem-pc-qcqs-derived-direct-image-right-adjoint` vs `def-pc-upper-shriek-right-adjoint`: the new node states existence for arbitrary qcqs morphisms; the existing definition only packages a chosen adjoint for proper Noetherian morphisms.

## Not duplicates

`lem-pc-perfect-generator-exists` vs `lem-pc-derived-qcoh-perfect-generation`: the new node asserts existence of one perfect generator; the existing node only asserts generation by the full class of perfect complexes.
`lem-pc-perfect-generator-pullback` vs `lem-pc-derived-qcoh-perfect-generation`: the new node asserts preservation of a chosen generator under affine pullback; the existing node has no pullback assertion.
`def-sc-duality-equation-base-change-map` vs `def-pc-base-change-map-cech`: the new definition is the mate map for right adjoints in a derived cartesian square; the existing definition is a Cech base-change map for direct images.
`lem-pc-base-change-rhom-perfect` vs `lem-pc-proper-support-perfect-direct-image`: the new node is algebraic RHom base change for a perfect complex; the existing node is geometric perfectness and direct-image base change.
`def-sc-duality-equation-base-change-map` vs `lem-sc-proper-flat-right-adjoint-affine-basechange`: the new definition constructs the canonical mate map used by the item; the item asserts that this map is an isomorphism.
`lem-pc-global-hom-adjunction` vs `lem-sc-proper-flat-right-adjoint-affine-basechange`: the new node is the adjunction isomorphism for arbitrary objects; the item is the stronger base-change isomorphism for a proper flat square.
`lem-sc-flat-precompose-pus` vs `lem-sc-proper-flat-right-adjoint-affine-basechange`: the new node states the transformation and its mate compatibility; the item proves the mate is invertible.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-affine-derived-pushforward-t-exact`: the new node is RHom base change for a perfect first argument; the existing node is t-exactness of affine derived pushforward.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the new node compares RHom after pullback; the existing node computes cohomology of a derived pushforward.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-finite-affine-derived-equivalence`: the new node is a perfect-complex Hom comparison; the existing node is the affine derived equivalence.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`: the new node concerns Hom under affine pullback; the existing node concerns acyclicity and pushforward cohomology.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-qcoh-acyclic-derived-sections-comparison`: the new node is RHom base change; the existing node compares derived sections with ordinary sections.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-affine-derived-concentration`: the new node is the Hom comparison for perfect complexes; the existing node is concentration of affine derived pushforward.
`lem-pc-affine-morphism-hom-out-of-perfect` vs `lem-sc-affine-derived-cohomology`: the new node is affine RHom base change; the existing node identifies cohomology of affine derived pushforward.

## Second reading by K1

- Item statement: checked against Tag 0AA8, Lemma 48.6.2, case (1); the affine bases, proper flat finitely presented morphism, cartesian square, right adjoints, and mate-map conclusion are all present.
- Step 1: checked flatness-to-Tor-independence and the affine derived-tensor calculation; the mate is supplied by `def-sc-duality-equation-base-change-map`, and the elementary calculation is limited to the stated affine charts.
- Step 2: checked the generator existence and affine pullback statements, and the Tag 0A1H direct-image input specialized to the proper morphism and the chosen perfect generator.
- Step 3: checked each RHom comparison against the statements of `lem-sc-flat-precompose-pus`, affine Hom base change, global adjunction, Tag 0A1H base change, and algebraic perfect RHom base change; the cited statements provide the named comparisons.
- Step 4: checked generator detection of a zero cone and the mate-defined map; the pulled-back generator is the object used for detection.
- `def-sc-duality-equation-base-change-map`: checked self-containment against the cartesian-square definition; all four maps `f`, `g`, `f'`, and `g'` and both adjunctions are now introduced explicitly.
- `lem-pc-perfect-generator-exists`: checked the quasi-compact, quasi-separated hypotheses and the localizing retract-closed generation conclusion against Tag 09IS; zero and affine-field cases are consistent.
- `lem-pc-perfect-generator-pullback`: checked affine pullback and generator hypotheses against Tag 09IS; identity and field-base-change cases are consistent.
- `lem-pc-affine-morphism-hom-out-of-perfect`: checked affine morphism, perfect first argument, arbitrary derived second argument, and the RHom comparison against Tag 0AVW.
- `lem-pc-global-hom-adjunction`: checked the right-adjoint and quasi-coherent derived-category hypotheses and both RHom arguments against Tag 0AA8 case (1).
- `lem-pc-base-change-rhom-perfect`: checked the ring map, perfect complex, arbitrary complex, and derived tensor RHom comparison against the cited algebraic base-change lemma.
- `lem-sc-flat-precompose-pus`: checked the cartesian square, flatness, right adjoints, transformation, mate, and compatibility clause against the final compatibility sentence of Tag 0AA8.
- Existing `lem-pc-proper-support-perfect-direct-image`: read its statement and confirmed it supplies perfectness and arbitrary base change for the direct image used in Steps 2 and 3; recorded as a tool use in the split report.
- DAG and blueprint searches: checked each new identifier and its nearest blueprint ancestor; no duplicate or blueprint restatement was found.
- Mathlib searches: verified the recorded LeanFinder, Loogle, and grep entries in `searches.jsonl`; no exact scheme-level declaration was found.
- Changes: repaired the map-definition statement to introduce `f`, `g`, `f'`, and `g'` explicitly, and added this second-reading record.
- Additional changes: corrected the item node's `created.item` and blueprint `via` fields to name this delivered item; added the existing `def-pc-generators` definition to both generator-node statements and dependency lists; and corrected the source-location record to the imported `duality.tex` file.
