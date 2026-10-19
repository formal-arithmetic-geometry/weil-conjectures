# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-excellent-normalized-blowup-tower.json: statement, split into eight steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-integral-blowup-projective-geometry.json: statement-only input, unsplit; no Mathlib match. Ordinary finite-type blowups of integral schemes are integral and projective in the bundle convention (02ND, 02NS).
- dag/nodes/sec-deligne-laumon-a1/lem-per-projective-bundle-composition.json: statement-only input, unsplit; no Mathlib match. General composition theorem with qcqs target (0C4P).
- citations.json: verbatim statement evidence for every step/node citation.

The item statement and all its statement dependencies are unchanged. No unit record needs modification: this is a technical child, not the unit's statement node. All proof steps are below 2000 characters.

## Attachments

None. I searched the project Lean source for the exact item id and the normalization/blowup/excellence notions. There is no declaration stating the item. WeilConjectures/Blowup/Affine/Projective.lean:125 gives a closed projective-space embedding for an affine blowup; it does not give integrality or the general global projective-bundle assertion. Its module docstring explicitly says global projectivity remains unformalized. WeilConjectures/Blowup/Proper.lean proves global properness, not the required projectivity. Neither can close this item or either new node.

## WANTED

None. All mathematical inputs used here have local Stacks sources.

## Audit and changes

The input was statement-only, with an extensive source list but no proof. I retained the complete statement, including arbitrary finite dimension d >= 1, the zero-length tower, the precise projective-bundle convention, preservation of every normal open avoided by the centers, and the explicit absence of a regular-endpoint assertion. No STATEMENT-DISPUTED correction was needed.

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's chapter/unit/node levels and human requirements, coord/delivery-errors.md B through E, coord/dag-sync.md, GOAL.md, the worker role, chapter and unit records, and the current blueprint unit and ancestor proof. The route is the geometry of an already chosen normalized-blowup tower inside the surface-resolution input, not an alternative proof of the perverse-sheaf unit.

Existing generic tools reused: excellent normalization preparation; componentwise normalization affine charts; affine stalks/function fields; integral-section extension on a normal scheme; excellence under finite type and on affine covers; finite morphisms are projective in the bundle convention; projective-bundle morphisms are proper; closed-dominant dimension; the blowup complement theorem; locally Noetherian schemes are quasi-separated. Their off-unit uses are declared individually in split_report.tool_uses.

The item Mathlib search and both new-node searches ran through msearch.py and are recorded exactly in searches.jsonl and mathlib_searches. Two natural-language phrasings were used for the ordinary blowup input and for projective composition. Loogle and the AlgebraicGeometry grep found no scheme blowup/projectivity assertion. Semantic hits give relative normalization, ordinary Proj properness, integrality of Spec, or composition of proper maps. These neither establish the global blowup statement nor projective-bundle composition. In particular IsProper.stableUnderComposition proves only properness. None of the new nodes is a Mathlib leaf.

## What remains

Nothing in this one-level split. The two new inputs are intentionally unsplit statement-only nodes. They are genuinely smaller geometric results, and contain no proof sketch hidden in their statements. No Lean was written or compiled. No repository or launcher file was edited.

## Review by Q19

I read Stacks resolve.tex, lemma-Nagata-normalized-blowup (0BFT), including its proof: the ordinary blowup is proper, its finite-type source is Nagata, and normalization is finite. I also read divisors.tex lemma-blow-up-integral-scheme (02ND), lemma-blowing-up-projective (02NS) and its symmetric-algebra/relative-Proj proof, morphisms.tex lemma-finite-projective (0B3I), lemma-composition-projective (0C4P), lemma-alteration-dimension (02JX), lemma-normalization-localization (035K), lemma-normalization-normal (035Q), lemma-nagata-normalization (035S), and more-algebra.tex lemma-finite-type-over-excellent (07QU). The source really uses the bundle convention for projectivity. 0C4P needs its target qcqs; the proof does not omit that assumption.

Step 1 uses lem-per-excellent-normalization-preparation exactly for finiteness, surjectivity, normal local rings, Noetherianness and excellence. Its reduced hypothesis holds because the input is integral. I opened lem-per-componentwise-normalization-affine-charts: its integral specialization has the single minimal prime (0), so it identifies the componentwise construction with the function-field normalization. I opened lem-weil-pbc-spec-domain-stalks-function-field: it supplies integrality of each Spec of the integral closure and identifies the zero-prime stalk with the fraction field. The argument in the step supplies irreducibility of the glued source and the equality of function fields; no finite-type-over-Q assertion from lem-trf-normalized-blowup-calculus is used.

Step 2 uses the exact statements of lem-trf-finite-projective-bundle and lem-trf-projective-bundle-proper, which apply to arbitrary finite morphisms and arbitrary bundle-projective morphisms. I checked the dimension lemma's assumptions individually: integral source and target by Step 1, dominant because the generic field map is an isomorphism, locally Noetherian target by hypothesis, locally finite type and closed because the map is proper. Its equality clause therefore has transcendence-degree term zero. No universal-catenary dimension formula is being imported without its hypotheses.

Step 3 uses lem-sbc-normal-dense-open-integral-section exactly as stated: W is locally Noetherian and normal, D(s) is a dense open, and a/s is an integral section on it. The extension has the same generic germ, so every element of the affine normalization ring was already in A. The chart and function-field nodes justify the affine identification and its fraction-field interpretation. The inverse maps glue by uniqueness of inverses. This proves normalization is an isomorphism on the entire normal open, not just some dense open.

Step 4 explicitly sets up the induction, with its base proved by Steps 1 and 2. The center is a supplied reduced closed subscheme, whose ideal is quasi-coherent by def-sbc-closed-immersion-ideal-sheaf (I opened its full statement, including its affine description and quasi-coherence clause). def-weil-pbc-noetherian-ring says every ideal is finitely generated. A closed point cannot be the generic point in positive dimension, so its ideal is nonzero. The ordinary-blowup node then supplies only the integrality and projectivity of B; it does not supply any normalized tower clause.

Step 5 uses projective-bundle properness, the proper and finite-type definitions, finite-type stability of excellence, its definition implying Noetherianness, and excellence detected on an affine cover. I opened each of those statements. The finite affine covers exist because the morphism is finite type and the target has a finite affine cover. Each chart algebra is excellent over its excellent target ring; excellent means Noetherian. The affine-cover theorem upgrades the cover property to every affine open. This supplies exactly the hypotheses for the next normalization, without any global affine base or ample line bundle.

Step 6 uses thm-nagata-global-blowup-complement exactly for the displayed restriction away from the center. That nonempty open contains the generic point, giving the field isomorphism. The dimension lemma then applies to b with the same checked proper/integral/locally-Noetherian hypotheses as in Step 2. Steps 1 and 2, now applied to B, give the new normalization and its dimension. A previous step can be reused as an argument; no new lemma equivalent to the item has been created.

Step 7 uses lem-weil-pbc-locally-noetherian-quasi-separated to supply quasi-separatedness, in addition to the explicit finite affine covers supplying quasi-compactness. The new general composition statement is applied first with target X_j and then target X. Both are qcqs. Step 8 uses the existing complement statement and the normal-open argument already proved in Step 3: the relevant open of B is isomorphic to U, and hence normal, before applying normalization over that open. This checks the actual inverse images in the tower, not merely containment of images as a substitute for a scheme factorization.

The first new node agrees hypothesis by hypothesis with 02ND and clause (1) of 02NS: integral base, nonzero quasi-coherent ideal, and finite type for projectivity. The second agrees with 0C4P for arbitrary schemes and retains the qcqs target assumption. They are statement-only, have every named notion defined or referenced, and were searched against the whole DAG, blueprint_refs.py (keywords and tags), blueprint text, and project Lean source before writing. Their sources' facts are non-elementary: global blowup projectivity uses relative Proj, and bundle-projective composition uses quasi-projectivity and properness. The item still contains the induction and the normalization/dimension/open calculations, so neither new node restates the item or its normalized-point-blowup clause.

Small cases checked: n=0; an already normal X; empty U; a length-one blowup on a regular curve (the center is Cartier so the ordinary blowup is the identity); blowup of (x,y) on affine two-space; a nonnormal excellent curve with nontrivial finite normalization; a non-affine Noetherian base lacking an ample line bundle. All use the same bundle convention. The restriction d>=1 is used precisely to rule out blowing up the entire one-point generic scheme with the zero ideal: Spec of a field and ideal zero would have empty blowup and would invalidate the field/dimension induction. This hypothesis was retained. There is no claim that an arbitrary normalized point blowup is regular.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the written files: unsplit children have no proof, every step's non-elementary input is named, citation quotes are verbatim statements, and the only long argument is broken into separate bounded steps. The main corrections during this self-review were to reuse the existing excellent normalization preparation, separate ordinary from normalized blowups, retain the qcqs requirement in composition, and prove the normal-open clause by the existing integral-section extension statement instead of citing a definition as if it asserted a theorem. No SGA source is used.

## Not duplicates

lem-per-integral-blowup-projective-geometry vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement assumes quasi-projectivity over an excellent affine base and concludes geometry of a normalized blowup; the new ordinary-blowup statement works for every integral scheme and does not normalize it.
lem-per-integral-blowup-projective-geometry vs lem-per-excellent-normalized-blowup-tower: the item concerns a normalized tower over a Noetherian excellent finite-dimensional base; the new input concerns one ordinary blowup with no excellence, Noetherianness or dimension assumption.
lem-per-projective-bundle-composition vs lem-per-excellent-normalized-blowup-tower: the item concerns a specific normalized-blowup tower; the new statement is a two-map projective composition theorem for arbitrary qcqs target schemes.
lem-per-integral-blowup-projective-geometry vs lem-trf-normalized-blowup-calculus: that node works only for reduced finite-type Q-schemes and normalized blowups and does not state arbitrary ordinary blowup bundle-projectivity.
lem-per-projective-bundle-composition vs lem-trf-h-projective-composition: the existing node concerns closed embeddings in finite projective spaces; the new theorem concerns finite-type quasi-coherent projective bundles and assumes qcqs target, without an ample line bundle.
lem-per-integral-blowup-projective-geometry vs thm-nagata-global-blowup-proper: the existing node states properness only, not bundle-projectivity or integrality.
lem-per-integral-blowup-projective-geometry vs lem-trf-smooth-center-blowup-geometry: the existing node assumes smooth Q-schemes and smooth centers and states smoothness and reduced strict transforms, not general ordinary blowup integrality and bundle-projectivity.
