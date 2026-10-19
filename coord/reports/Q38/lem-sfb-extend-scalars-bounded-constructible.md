# Q38 stage-1 report: lem-sfb-extend-scalars-bounded-constructible

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-extend-scalars-bounded-constructible.json: existing statement node split in six steps; statement and statement dependencies unchanged; no Mathlib match.
- citations.json: all 18 step/node citations, each with a verbatim quotation from the cited statement.
- report.md: this report. searches.jsonl is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0. No unit file is changed: this item is the preservation lemma in step 2 of the rationalization unit, not the unit's key localization statement.

## Attachments

None. The exact name AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj and blueprint id were searched throughout /home/ubuntu/weil-src-slopmaster2/WeilConjectures; neither occurs there. Concept searches for constructibility and extension of scalars produced no exact project theorem. In the read-only upstream master, WeilConjectures/CategoryTheory/ModuleObjects/EllAdicRationalization.lean:118–124 states precisely the item, with proof `sorry` at line 124, so it is not an attachment. The node itself has no lean_audit record and says the blueprint declaration was not found. Discrete-coefficient pro-étale constructibility results in slopmaster2 are not the internal modules over the condensed coefficient ring objects here.

## WANTED

None. The proof follows the current blueprint's explicit localization/flatness/local-presentation argument, with its generic missing interfaces supplied by existing DAG nodes. No SGA source is used.

## What was wrong and what changed

The imported proof was not a complete citation split: its flatness step had no uses and elementary=null, while its first and last steps cited only definitions for several substantive assertions. Reproving the localization construction would duplicate det-prop-sfb-qlbar-colimit-x-invert-ell, which already states the precise inclusion and flatness. I replaced that part by the existing statement. I then cited the actual preservation-of-homology statement rather than treating a coefficient-change definition as that theorem.

The constructibility paragraph originally established finite local presentation without tracking scalar entries. The current sk-def-sfb-constructible and det-def-sfb-constructible-local-model require matrices from the scalar ring, a stronger condition than an arbitrary matrix over the coefficient sheaf. The new proof takes a matrix over O_E and proves its image is the same matrix over E. It does not infer a constant local model from mere finite local presentation. It also treats an arbitrary scheme affine locally, rather than assuming that it has a finite global stratification. These repair the proof, and do not change the item's statement or add hypotheses.

The exact master Lean declaration uses the generic boundedConstructible predicate; the imported neighboring def-sfb-constructible-module uses locally finitely presented modules, whereas the reviewed current sk-def-sfb-constructible specifies finite constant local models. This delivery proves preservation for the latter, stronger notion as explicitly required by the item's statement dependency; its same presentation calculation also preserves the former notion. No comparison or silent identification of those definitions is needed or claimed.

## Existing nodes and route

Before considering any new node, I searched DAG titles/statements for extension of scalars, exact functors, strong monoidal inverse image, flatness, finite constant local models, filtered colimits and homology. Whole-blueprint searches were run for "extension of scalars", "preserves homology", "finite presentation", "commutes with restriction", "flat change" and "exact functor"; ancestor identifies this item itself. These recover the existing localization lemma, homology lemma and local-model matrix equivalence. No other blueprint node states the entire preservation theorem. No new node was needed, so there are no same-tag pairs for a Not duplicates section.

The chapter sec-proetale-coefficients and unit sk-thm-sfb-rationalization-comparison records were read in full. This lemma realizes the bounded-constructible assertion in unit step 2, retaining its integral-to-rational coefficient route. Definitions and generic tools of other units are described in the second-reading section for the maintainer's route review. In particular lem-weil-pbc-left-adjoint-preserves-colimits is applied only to the finite coequalizer indexing category. Neither a direct-image comparison nor the localization theorem on bounded constructible categories is used circularly. A transitive statement/proof dependency traversal of the cited interfaces found no path back to the item.

## Mathlib research

All searches were made using the required msearch.py command and the actual query texts/results are recorded in the item and searches.jsonl. LeanFinder, Loogle, LeanSearch and source grep all ran successfully. A second semantic phrasing checked an exact change of coefficients and local finite presentations, rather than merely searching the l-adic name. Loogle and the first grep found no constructible extension-of-scalars theorem. The semantic results include ordinary ModuleCat flat-extension exactness and SheafOfModules.Presentation.map; these do not supply the whole theorem for these internal coefficient ring objects and bounded constructible derived complexes. I read Mathlib/Algebra/Category/ModuleCat/Descent.lean:34–46 and Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:29–125 to check these objects and presentation notions. The second grep located the flat-extension declaration at Descent.lean:42. No result was promoted to a Mathlib leaf; the proof uses already existing DAG interfaces rather than creating a general fact Mathlib might already have.

## Review by Q38

I read the statement and full .proof.md of the current main-20261015 blueprint item, the chapter/unit records, and the statements of every cited node. I also compared the upstream master declaration at EllAdicRationalization.lean:118–124, including its finite intermediate-field and prime variables at line 89. The theorem is about arbitrary schemes, a finite extension E of Q_l with its specified integral inclusion, unbounded ambient derived categories and bounded constructible objects; it has no invertibility-on-X, Noetherianity or derived-completeness hypothesis. The unchanged statement agrees with that source. There are no new nodes needing source review.

Step 1 uses def-sfb-integers-to-subfield for the actual condensed inclusion pulled to every scheme; det-prop-sfb-qlbar-colimit-x-invert-ell explicitly concludes that E_T is flat over O_{E,T} for every scheme T; lem-sfb-modobj-extension-right-exact explicitly supplies finite-colimit preservation. I checked that flatness is for this inclusion, and that the all-schemes quantifier required in the next lemma is verified, not just the fixed X. I removed the unsupported original filtered-colimit/sheaf computation and reused the existing stronger statement.

Step 2 uses lem-sfb-extend-scalars-preserves-homology, whose statement explicitly says preservation of homology for coefficient changes preserving finite limits at every scheme, and sk-def-sfb-derived-extension-of-scalars, whose statement explicitly computes the derived functor on a K-flat resolution. The displayed chain H(FP)=F(H(P))=F(H(K)) is exactly what those statements give. There is no bounded-below restriction and no appeal to a theorem about only discrete coefficients.

Step 3 uses sk-def-sfb-module-pushforward-pullback for the strong monoidal abelian inverse image and its right adjoint; lem-weil-pbc-left-adjoint-preserves-colimits for preservation of the defining coequalizer; def-sfb-modobj-extension for its two arrows; sk-prop-sfb-cartesian-coefficients for both coefficient identifications and exact inverse-image interpretation of module restriction; and sk-def-sfb-coefficient-change for the commuting coefficient square. All five statements were opened, and each says the specific property used. The proof writes the image coequalizer and identifies both arrows and the resulting S_T-action. The diagram is finite, so the colimit lemma's small-index hypothesis is satisfied. The ring isomorphisms apply to both O_E and E, which are admissible coefficient rings, and no assertion about arbitrary noncartesian ringed topoi is made.

Step 4 is elementary from the balanced tensor definition and finite-colimit preservation: the two maps giving S tensor_R R = S are written and their composites follow from balancing and the unit; finite coproducts give all finite free ranks. The matrix calculation explicitly sends each scalar a_ij to its image in E, which is essential for the current local-model definition. This is why I kept it as an elementary step rather than creating a new preservation-of-presentations node.

Step 5 uses sk-def-sfb-constructible for constructible strata and its affine-local definition, det-def-sfb-constructible-local-model for the two directions of the finite-scalar-matrix characterization, and lem-sfb-modobj-extension-right-exact for the cokernel. I checked both directions in the statement of the local-model node: it really states the equivalence and does not merely define finite presentation. The pullback used is along U_ai to V_a to V to X, an arbitrary scheme morphism allowed in step 3. The original stratification and covering family are retained, so constructibility of strata and the covering condition need no new geometric lemma. Working on each affine V avoids imposing qcqs or a global stratification on X. The corrected calculation retains constant entries; an arbitrary coefficient-sheaf matrix would not suffice.

Step 6 is elementary from the displayed homology isomorphism, step 5 and sk-def-sfb-bounded-constructible, which explicitly requires both a common finite cohomological interval and constructibility in every degree. Finite-colimit preservation includes zero. It follows that the same interval works; no uniform bound across strata or across covers is inferred.

For B–E I checked that there are no renamed clauses/new nodes, no statement-only node carrying a hidden proof, no unverifiable or proof-internal citation, and no cycle introduced by the chosen dependencies. I retained all imported metadata. Edge cases checked: the zero complex and zero module; rank-zero presentations; free rank-one modules giving E_X; O_E/l^r local models giving zero after rationalization; empty schemes/strata; a shifted single sheaf; arbitrary non-qc/non-Noetherian X treated on affine opens. The scalar-matrix argument works for torsion models as well as free ones and does not assume that a finite-presentation module is projective. Every citation is supplied verbatim in citations.json. The substantive corrections were the full quantifier check for flatness, explicit identification of the pullback coequalizer arrows, scalar entries of local matrices, and affine locality.

## What could not be finished

Nothing remains in this one-level split. The existing unsplit generic interfaces remain independent future items; this task neither claims them proved nor edits them. 

## Second reading by Q38

- Item statement checked hypothesis by hypothesis against main-20261015 `lem-sfb-extend-scalars-bounded-constructible.md` (order 1648), its three-paragraph proof, `def-sfb-integers-to-subfield`, and upstream master EllAdicRationalization.lean:89,118–124: arbitrary scheme, prime ell, finite intermediate field E with its integral inclusion, and bounded constructible input; verdict: the current blueprint statement is unchanged and no extra hypothesis is used. The previously documented difference between the current blueprint local-model definition and the older Lean predicate remains explicit.
- Step 1 checked against `def-sfb-integers-to-subfield`, `det-prop-sfb-qlbar-colimit-x-invert-ell`, and `lem-sfb-modobj-extension-right-exact`: the coefficient map, all-schemes flatness, finite-limit preservation, and finite-colimit preservation are stated by those nodes; verdict: sound.
- Step 2 checked against `lem-sfb-extend-scalars-preserves-homology`, `sk-def-sfb-derived-extension-of-scalars`, and `def-sfb-left-derived-exact` (blueprint order 1613; slopmaster2 MapDerivedCategory.lean:77–86): homology preservation applies for every scheme after step 1, and the exact-functor comparison identifies the derived functor with the termwise one; verdict: repaired to cite this comparison directly, including for unbounded complexes.
- Step 3 checked against the five cited module-pullback, colimit, tensor, cartesian-coefficient, and coefficient-change statements: each supplies the displayed coequalizer comparison and both action maps; verdict: sound for an arbitrary scheme morphism.
- Step 4 checked against `def-sfb-modobj-extension` and `lem-sfb-modobj-extension-right-exact`: the balanced tensor calculation gives rank zero and finite free ranks, and the matrix entries are explicitly carried through the scalar map; verdict: elementary and sound.
- Step 5 checked against `sk-def-sfb-constructible`, `det-def-sfb-constructible-local-model`, and finite-colimit preservation: the same affine-local strata and covers work, and the local matrix remains scalar-valued after extension; verdict: sound without a qcqs or projectivity assumption.
- Step 6 checked against `sk-def-sfb-bounded-constructible`, step 2, and finite-colimit preservation: the common cohomological interval and constructibility of every cohomology sheaf are exactly the definition; verdict: elementary and sound.
- New nodes: none; there are no B1--B7 node statements to review. Existing-node searches and Mathlib searches are recorded in the worker sections and `searches.jsonl`; no duplicate or Mathlib leaf was introduced.
- Edge cases checked against the definitions and the six steps: zero complex and zero module, rank-zero and rank-one presentations, torsion local models, empty schemes and strata, a shifted single sheaf, and arbitrary non-qc/non-Noetherian schemes handled affine locally; verdict: no statement failure.

Changes: step 2 now cites the existing exact-functor derived comparison explicitly and uses a representing complex, avoiding an unnecessary choice of K-flat resolution. All 18 citations were refreshed from the current cited statements. Removed the worker-written `split_report.tool_uses`; these are proposals for maintainer assessment, recorded below instead. No statement change or new node was needed. Independently ran Loogle with `"constructible", "tensor"`: zero hits, recorded by msearch.py in searches.jsonl.

Proposed generic uses for the maintainer (no tool-use exemption is asserted):

- `det-prop-sfb-qlbar-colimit-x-invert-ell`: The unit explicitly uses this localization/flatness result; it provides the exact sheaf-theoretic coefficient map needed in step 1.
- `lem-sfb-modobj-extension-right-exact`: Generic finite-colimit preservation for internal extension of scalars; used on finite free presentations, not as a substitute for the rationalization argument.
- `lem-sfb-extend-scalars-preserves-homology`: Generic flat coefficient-change homology statement, applied after checking its all-schemes hypothesis; the unit contains no separate homology lemma.
- `sk-def-sfb-module-pushforward-pullback`: The ordinary module pullback and strong monoidal abelian inverse image supply the coequalizer computation, not a new route to rationalization.
- `lem-weil-pbc-left-adjoint-preserves-colimits`: Generic adjunction theorem applied only to a finite coequalizer diagram for abelian-sheaf inverse image; no coefficient/geometry hypotheses are imported.
- `sk-prop-sfb-cartesian-coefficients`: Generic identification of pulled-back coefficient sheaves, needed on the same strata and cover members as the local model.
- `sk-def-sfb-coefficient-change`: The naturality square identifies the two arrows of the pulled-back balanced tensor for the integral-to-rational coefficient map.
- `sk-def-sfb-constructible`: The constructible-sheaf definition is used with its affine-local clause and finite constant local models.
- `det-def-sfb-constructible-local-model`: The existing equivalence between constant local models and matrices with scalar entries is used in both directions; no replacement of the local-model notion.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q38 lem-sfb-extend-scalars-bounded-constructible --no-push` printed `OK (not pushed)` at temporary delivery commit 5f5dd542d7: preflight passed. No delivery was pushed. This report now includes that result; the same command is rerun on the final sandbox before the READY handoff.

Second-reader validation: the repaired sandbox passed `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q38 lem-sfb-extend-scalars-bounded-constructible --no-push` at temporary commit `de245918ac` with `OK (not pushed)` and preflight passed. The installed launcher accepts no positional trailing dot, so the supported command form was used. The final delivery command reruns preflight on the complete report.
