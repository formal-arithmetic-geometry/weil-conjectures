# Stage 1 report: lem-weil-pbc-etale-shriek-relative-mayer-vietoris

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-shriek-relative-mayer-vietoris.json` — existing statement split retained; status changed to `split`; no new nodes.
- `citations.json` — 25 step/node entries, with verbatim quotes copied from the cited node statements.
- `report.md` — this report.

## Attachments

No attachment. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, the Mayer–Vietoris declaration name, and the relevant shriek/relative Mayer–Vietoris names. The exact declaration recorded in the DAG's later `lean` metadata is absent from this required slopmaster2 source checkout, so that metadata is not treated as a finished proof.

## WANTED

None.

## What I checked and corrected

The item was already split in the repository by the preceding worker and had no new child nodes to create. I copied that node, retained its statement, proof, dependencies, blueprint ancestry, source references, and recorded searches, and changed only its stage status from `unsplit` to `split` for delivery. The split follows Tags 0GKN and 0GKK in `literature/stacks-project/more-etale.tex`, with the compact-support composition identification from Tag 0F7J. No statement or hypothesis was changed. I checked the finite-ring coefficient category, the bounded-below condition, the quasi-compact open-cover hypotheses, and the use of independently chosen compactifications against the item statement.

The five proof steps were checked against the cited node statements. Step 1 uses `lem-weil-pbc-quasi-separated-affine-cover-criterion` for quasi-compact affine intersections, `lem-weil-pbc-qcqs-morphism-permanence` for quasi-compactness and finite-type permanence, `def-weil-open-immersion` for the open immersions, and `def-weil-pbc-scheme-conventions` for the scheme/morphism conventions. Step 2 uses the existing `lem-weil-pbc-etale-constant-ring-module-equivalence`, `lem-weil-pbc-extension-by-zero-adjunction`, `lem-weil-pbc-extension-by-zero-stalks`, `lem-weil-pbc-module-sheaves-colimits-forgetful`, `prop-weil-pbc-geometric-stalks-exact`, and `lemma-weil-pbc-geometric-stalk-conservative`; each cited statement supplies respectively the coefficient identification, adjunction/counit, stalk formula, exact faithful forgetful functor, exact stalks, and stalk conservativity used in the explicit signed stalk calculation. I checked both point cases (points in `U∩V` and points in exactly one open), including the maps `(1,-1)` and `(1,1)`.

Step 3 uses `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-extension-by-zero-exact`, `lem-weil-pbc-module-sheaves-grothendieck-abelian`, and `lem-weil-pbc-complex-ses-triangle`; these statements give exact termwise restriction/extension, the abelian category, and the distinguished triangle from the short exact sequence of complexes. Step 4 uses `lem-weil-pbc-extension-by-zero-exact`, `lem-sf-exact-functor-derived-triangulated`, `lem-weil-pbc-module-sheaves-grothendieck-abelian`, `lem-weil-pbc-kinjective-functorial-existence`, `lem-weil-pbc-module-direct-image-left-exact`, `lem-pc-right-derived-functor-triangulated`, `lem-weil-pbc-derived-functor-negative-vanishing`, and `def-weil-pbc-projection-compactification`; I verified that these provide the exactness, K-injectives, left exact direct image, triangulated right derived functor, bounded-below preservation, and definition of the chosen compact-support functor. Step 5 uses `def-weil-pbc-projection-compactification`, `lem-weil-pbc-etale-shriek-qcqs-composition`, and `def-weil-triangulated-category`; I checked that the identity compactifications for the open immersions and the stated natural composition isomorphisms transport the triangle to the three independently chosen candidates, and that the displayed conjugation formulas are an isomorphism of triangles.

I also inspected the only proof step longer than 2000 characters (step 2). It is one explicit stalkwise short-exactness argument, with every non-elementary input cited above; it does not hide an additional independent comparison lemma or a restatement of the item. The item has no new definitions, no duplicate child nodes, and no Mathlib leaf claims.

## Review by NJ

I read the item source `literature/stacks-project/more-etale.tex`, Tags 0GKN and 0GKK, and the Tag 0F7J composition reference, as well as the source recorded on every cited node. For each of the five steps I opened the cited node files and verified that the quoted statements in `citations.json` actually state the facts used: qcqs and finite-type permanence in step 1; coefficient equivalence, extension-by-zero adjunction and stalks, forgetful exactness, stalk exactness and conservativity in step 2; exact inverse image, exact extension by zero, Grothendieck abelian structure and the complexes triangle in step 3; derived-functor hypotheses and bounded-below preservation in step 4; and compactification composition plus triangulated transport in step 5. The hypotheses I checked include finite commutative coefficients, separated finite-type `f`, qcqs source and target, quasi-compact opens with `U∪V=X`, and bounded-below `K`. I corrected the copied item only by setting its status to `split` and added the required verbatim citation map; no mathematical clause was altered.

## What could not be finished

Nothing. The required source checkout contains no exact finished declaration, so this is a split delivery rather than an attachment.
