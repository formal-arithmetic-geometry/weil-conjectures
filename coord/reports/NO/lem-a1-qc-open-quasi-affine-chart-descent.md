## Worker report

Files written:
- dag/nodes/sec-purity-real-sheaves/lem-a1-qc-open-quasi-affine-chart-descent.json: statement, split; not a Mathlib leaf. Five proof steps, no new nodes. Original statement and statement dependencies retained.
- citations.json: one entry for every step citation, quoting the cited statement verbatim.
- searches.jsonl: genuine msearch.py results for this item, including two semantic phrasings, LeanSearch, Loogle, and source grep.
- report.md: this report and self-review.

Attachments: none. Searched lean/WeilConjectures for the exact blueprint id and ind-quasi-affine terminology, and inspected the quasi-affine declarations in WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean. Its IsQuasiAffineHom definition and the instance for a quasi-compact map from an already quasi-affine source do not prove descent for all quasi-compact opens. No exact completed project declaration was found.

WANTED: none.

Problems in the imported node: no statement defect found. It had no proof. The compactness of chart restrictions must follow from K -> V, using V quasi-separated, rather than from an unjustified assumption that f is quasi-compact or that an intersection of target charts is affine. The proof now makes this explicit. It specializes the argument of Stacks 0F1U to the item's affine charts, so the more general quasi-affine cancellation argument for qcqs (possibly non-affine) charts is unnecessary. Nothing was left unfinished.

## Sources and existing-node searches

Read Stacks more-morphisms.tex, Tag 0AP6 (definition-ind-quasi-affine) and Tag 0F1U (lemma-ind-quasi-affine-alternative-definition), including its entire proof. Read schemes.tex Tag 03GI (lemma-quasi-compact-permanence) and Tag 01IT (lemma-basis-affine-opens), and morphisms.tex Tag 01SM (lemma-characterize-quasi-affine), statement and proof. Read the current main-20261015 ancestor lem-a1-affine-hc0 and the chapter/unit records; this is a tool argument below that unit, on the existing Gabber ancestry, not a modification to a unit step.

The DAG/blueprint search used blueprint_refs.py ancestor and searches for quasi-affine and affine open, plus DAG searches by 0F1U, quasi-affine, affine-open basis and quasi-compactness permanence. The existing lem-a1-quasi-affine-target-locality states precisely the cover criterion needed here; lem-weil-pbc-affine-opens-basis states the refinement assertion; lem-weil-pbc-qcqs-morphism-permanence supplies compactness of the induced map. All were reused. No new node is needed for the definition-level compactness and open-subscheme restriction argument.

The item-level searches are appended to its earlier search records, which are retained as inherited provenance. All new entries were executed with the required msearch.py command and read. HasAffineProperty.iff_of_openCover assumes the HasAffineProperty instance; it does not establish locality of the ind-quasi-affine condition. IsQuasiAffine.of_isImmersion assumes its ambient scheme is already quasi-affine. Scheme.exists_isQuasiAffine_of_isLimit concerns inverse systems, absent here. Reading Mathlib/AlgebraicGeometry/QuasiAffine.lean confirms that its definition and immersion theorem do not state the item. The grep restricted to that file printed malformed file labels (the single-file rg output omits the filename); the raw log is retained faithfully and the source itself was read. The separate ind-quasi-affine grep returned no hits. No unavailable service was treated as evidence of absence.

## Not duplicates

There are no new nodes. The item is not a duplicate of lem-a1-quasi-affine-target-locality: the latter assumes quasi-affineness of the entire inverse images of a chosen cover, whereas the item assumes it for compact opens of possibly noncompact inverse images and must establish compactness after restriction to a new target open. It is not the finite affine enlargement/base-change node: no change of base is needed in this argument.

## Review by NO

I read the item and each cited node alongside the Stacks sources. The statement agrees with 0F1U (3) -> (4) after converting the affine-chart hypothesis to absolute quasi-affineness. All quantified opens are open subschemes with the restricted structure sheaf; no reduced induced structure or image factorization is being substituted. K is compact, V is quasi-separated, and there is no finite-type, compactness or separation hypothesis on f. The specified compactness of V is preserved, although the argument does not need it.

Step 1 uses exactly clause (1) of lem-weil-pbc-qcqs-morphism-permanence: its statement explicitly says that a compact source mapping to a quasi-separated target gives a quasi-compact map. Here the source is K and target V. This is the specialization of 03GI with V -> Spec Z. It does not require K to be separated.

Step 2 uses the actual neighbourhood assertion in lem-weil-pbc-affine-opens-basis, not a result extracted from its proof. Apply it on Y to each v in V intersect U_i. Its statement gives v in W contained in that intersection with W affine, so the pairs (i,W) cover V. The intersection itself is neither claimed affine nor claimed compact. The collection is a set (I and the opens of Y are sets), so no large-index existence assertion is hidden here.

Step 3 uses the quasi-compactness clause of def-weil-finite-type-morphism, which explicitly defines a quasi-compact morphism by compact inverse images of affine opens. W is affine by step 2 and h is quasi-compact by step 1, so L is compact. As subsets, L = K intersect f^{-1}(W) lies in f^{-1}(U_i). K and f^{-1}(W) are open in X, so L is an open subscheme of that inverse image with precisely its induced structure. The hypothesis of the item now applies to L. This is an elementary use of a definition and a hypothesis; no non-elementary preservation theorem is left uncited.

Step 4 invokes the reverse implication of lem-a1-quasi-affine-target-locality. Its statement requires only a scheme morphism, an affine open cover, and quasi-affine inverse-image schemes. All three have been supplied. In particular it imposes no additional separation, finite-type, or compactness hypotheses. It lives in the item's own unit, so no off-route tool declaration is needed. The forward implication is not being used to infer its converse.

Step 5 applies the actual definition in def-nagata-quasi-affine-morphism to the affine open V of itself; its inverse image is K. This establishes every clause, including the last absolute-scheme clause, with no new definition of quasi-affineness.

Small cases: if K is empty, each L is empty and is the open subscheme of Spec(0), so the chart hypothesis and locality argument apply. If V is empty then K is empty; the affine cover may be empty and locality still has its stated meaning. If I is empty, Y, V and K are empty. Infinite covers cause no problem: no finite subcover is used to impose a uniform property. For the non-separated test Y equal to the affine line with doubled origin and f = id, the usual affine-chart hypothesis holds, and K = V = Y produces the quasi-affine morphism id without falsely asserting that Y is an absolute quasi-affine scheme; the final absolute assertion is used only when V is affine. A non-quasi-separated ambient Y also causes no problem when V is qcqs, since the sole compactness-permanence invocation is over V.

No new statements require additional small-case checks. Every non-elementary proof input has a cited node, every citation was opened, and citations.json copies an actual part (here the full statement) of each one. No proof step exceeds 2000 characters and none hides an intermediate lemma. No statement correction, SGA source, new node, Lean writing, or compilation was used. The correction made during self-review was to use the existing compact-map definition directly for the restricted inverse images; this avoids an unnecessary base-change detour and its extra hypotheses. The required server dry run follows this report.
