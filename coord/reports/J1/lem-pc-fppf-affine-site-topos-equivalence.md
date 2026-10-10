1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-fppf-affine-site-topos-equivalence.json` (statement, split; Mathlib generic dense-subsite theorem cited in a child node).
- `dag/nodes/sec-picard-framework/lem-pc-fppf-affine-open-cover.json` (statement, Mathlib leaf: `AlgebraicGeometry.Scheme.instInhabitedOpenCover`).
- `dag/nodes/sec-picard-framework/lem-pc-fppf-affine-refinement.json` (statement, no Mathlib match; Stacks Tag 021V/021S fact).
- `dag/nodes/sec-picard-framework/lem-pc-fppf-dense-sheaf-equivalence.json` (statement, Mathlib leaf: `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`).
- `citations.json` (verbatim statement quotes for every proof citation).

2. Attachments: none.

3. WANTED: `literature/stacks-project/topologies.tex`, Tag 021V (the repository contains only the citation metadata, so the proof follows the cited Stacks statement and the imported blueprint).

4. No statement error was found. The original item had no proof or proof dependencies; its two geometric density clauses and the sheaf-equivalence consequence were made explicit. The affine refinement was kept as a separate Stacks-sourced statement because it is the substantive affine-site input. The generic dense-subsite result was searched in Mathlib and recorded as a leaf rather than reproved.

## Not duplicates

`lem-pc-fppf-affine-open-cover` vs `lem-weil-pbc-etale-covering-affine-refinement`: the former is an affine open cover of an arbitrary scheme, while the latter refines an etale family over an affine target and retains etale morphisms.
`lem-pc-fppf-affine-refinement` vs `lem-weil-pbc-etale-covering-affine-refinement`: the former concerns fppf families and affine-open refinements; the latter concerns etale families and uses the etale morphism property.
`lem-pc-fppf-dense-sheaf-equivalence` vs `lem-pc-dense-subsite-sheafification-compatibility`: the former is the equivalence of sheaf categories, while the latter is the compatibility isomorphism between sheafification and restriction assuming that equivalence.
`lem-pc-fppf-affine-refinement` vs `lem-pc-fppf-affine-site-topos-equivalence`: the refinement node is the affine-target geometric input with explicit finite affine opens and factorizations; the item additionally asserts full faithfulness, cover density for all objects, and the sheaf-topos equivalence.
`lem-pc-fppf-affine-refinement` vs `lem-pc-picard-functor-agrees-sc`: the refinement node concerns arbitrary fppf covering families over an affine scheme; the Picard node compares two Picard presheaves and only invokes Tag 021S through the site comparison.
`lem-pc-fppf-affine-refinement` vs `def-pc-fppf-site`: the refinement node is an existence theorem refining a covering; the definition node only defines fppf coverings as flat morphisms locally of finite presentation.
`lem-pc-fppf-affine-refinement` vs `lem-pc-fppf-affine-sheafification-restriction`: the refinement node constructs affine refinements of coverings; the sheafification node states the induced canonical sheafification isomorphism.

## Review by J1

I checked the item against the imported source citation, Stacks Topologies Tag 021V (Lemma 34.7.11), and the blueprint proof step named in the item. The item hypotheses introduce a scheme S, the affine fppf site, and the big fppf site; the proof uses the definitions `def-pc-scheme` and `def-pc-fppf-site` exactly for those objects. Step 1 verifies full faithfulness from the fact that the affine site is a full subcategory. Step 2 cites the affine-open-cover child, whose statement gives affine opens jointly covering every scheme, and checks that open immersions are fppf by the definition of the big fppf topology. Step 3 cites the affine-refinement child verbatim; its statement supplies finite affine opens inside members of the original fppf family, with fppf composites jointly covering the affine target. Step 4 checks that these clauses give cover density and the induced topology, then cites the Mathlib dense-subsite equivalence statement for both sets and abelian groups.

For the new nodes I searched the DAG and blueprint for affine-cover, affine-refinement, and dense-subsite statements before creating them. The affine-open-cover node matches `Scheme.instInhabitedOpenCover`; the refinement node has no Mathlib match after LeanFinder, Loogle, grep, and unavailable LeanSearch searches; the dense-subsite node matches `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`. I tested the statements on an affine scheme (where the identity open is a cover) and on a general scheme via its affine open cover. All citation quotes in `citations.json` are copied verbatim from the cited node statements.

5. Nothing remains unfinished beyond the unavailable local copy of `topologies.tex`; the Stacks tag and label are recorded in the node source fields.

## Second reading by J1

- Item statement: checked against Stacks Tag 021V, Lemma 34.7.11; full faithfulness, affine fppf refinements, affine open covers, and the topos equivalence match hypothesis by hypothesis.
- Item step 1: checked the full-subcategory argument against `def-pc-fppf-site` and `def-pc-scheme`; verdict elementary and correctly cited.
- Item step 2: checked against Tag 021V's affine-open-cover clause and the fppf definition; `lem-pc-fppf-affine-open-cover` supplies the cover and the open-immersion fppf observation is elementary from the stated definition.
- Item step 3: checked against Tag 021P, Lemma 34.7.4; the finite affine open refinement and fppf composites are exactly the cited node's conclusion.
- Item step 4: checked the induced-topology and dense-subsite hypotheses against the preceding clauses and Mathlib `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`; the sets and abelian-sheaf conclusions are the stated specialization.
- Node `lem-pc-fppf-affine-open-cover`: checked against Mathlib `Scheme.affineOpenCover` in `AlgebraicGeometry/Cover/Open.lean:140`; verdict exact Mathlib leaf, with searches recorded.
- Node `lem-pc-fppf-affine-refinement`: checked against Stacks Tag 021P, Lemma 34.7.4 (including the finite index set and open-affine refinement); verdict correct unsplit statement, with no Mathlib match.
- Node `lem-pc-fppf-dense-sheaf-equivalence`: checked against Mathlib `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` in `DenseSubsite/Basic.lean:797`; verdict correct generic leaf under its stated hypotheses.
- Small cases: tested an affine scheme (identity affine cover), a field spectrum, the empty scheme, and the zero-index edge for the covering formulations; no contradiction found.
- Changes: corrected the affine-refinement source from the incorrect `021V/021S` attribution to Stacks Tag `021P` (the lemma actually used), and recorded this verification section.
