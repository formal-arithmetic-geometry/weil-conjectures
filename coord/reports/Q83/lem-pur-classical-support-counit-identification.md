## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-pur-classical-support-counit-identification.json`, this report, and `citations.json`. The item is split in five steps. No new nodes; no new Mathlib leaves. The sandbox also contains the genuine search log and the script used to write the JSON.

Attachments: none. Searches for the exact blueprint tag in `lean/WeilConjectures/` found no declaration. Concept searches located `SixFunctors/OpenClosed/SupportsDerived.lean`, notably `exists_iso_supportLocalizationTriangle` and `exists_supportLocalizationTriangle_iso_of_isGE`, but these concern etale support/exceptional triangles, rather than the arbitrary given ordinary pro-etale module triangle and all clauses of this item. Thus they do not attach this node. The existing pro-etale closed full-faithfulness declaration is already represented by its own node; it was not duplicated.

WANTED: none.

The input statement is unchanged and no dispute is raised. Its proof was empty. I retained its original source, blueprint ancestry, citations/searches and creation record. The proof now distinguishes the arbitrary completion of a triangle map from the unique transpose specified by the adjunction. It explicitly establishes derived full faithfulness before using uniqueness: the sheaf full-faithfulness statement alone would not suffice. The boundary square comes from signed rotation and TR3; it is not inferred merely from an isomorphism of the three objects.

Five new executed queries (LeanFinder in two formulations, Loogle, grep, LeanSearch) were read and appended verbatim to `mathlib_searches`; the earlier imported records remain. The general triangulated adjunction hits do not supply the geometric support assertion. The triangle isomorphism facts returned by Loogle are already covered by the existing DAG leaves. No service failure was disguised as absence.

Unfinished: none in the one-level split. The cited existing nodes remain responsible for their own proofs.

## Blueprint and route

I read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-prop-a1.json`, the current `main-20261015` proof at `sec-six-functors-basics/sk-prop-a1/sk-prop-a1.proof.md`, and the nearest blueprint ancestor `prop-pur-affine-line-orientation-uniqueness`. This item makes precise the identification of the supported localization term and its boundary used before applying direct image in that proof. It changes neither the unit nor its route. The source proof supplies the localization setting, while the five-step comparison argument is expressly marked agent-written and uses Stacks categorical axioms.

The only off-route non-leaf theorem used as a generic tool is `lem-exc-proetale-closed-fully-faithful`: it gives the sheaf counit isomorphism for arbitrary closed immersions and ordinary finite constant-ring module sheaves. It is declared in `split_report.tool_uses` for maintainer review. The exact-derived adjunction is an existing definition/construction, and both triangle lemmas are existing Mathlib leaves. The support-localization triangle is already on the unit's route through `sk-prop-a1-kummer`.

## Not duplicates

No new nodes are proposed. Whole-DAG statement/title searches and whole-blueprint searches (`triangle`, `fully faithful`, `supported triangle`, `counit`, `first arrow`, `exact derived adjunction`) located the existing closed full-faithfulness, support, exact-derived adjunction and triangle-isomorphism nodes used here. Neither the orthogonal-counit normalization lemma nor the etale comparison statements state this item with its given triangle and specified boundary.

## Review by Q83

I read Stacks `derived.tex`, Tag 0145 (`definition-triangulated-category`, specifically TR2 and TR3), Tag 014A (`lemma-third-isomorphism-triangle`, including its Hom/five-lemma proof), Tag 0144 (`definition-triangle`), and Tag 015F (`lemma-right-derived-exact-functor`). I also read `proetale.tex` Tags 09AA (`lemma-closed-immersion`) and 09BM (`lemma-closed-immersion-complement-retrocompact-exact`) and the existing localized-adjunction construction at `lean/Sheaf/SixFunctors/OpenTensorNormalizationData.lean:533`. There are no new-node sources to review. No SGA source is used.

Step 1 uses the exact inverse image and actual sheaf adjunction in `def-weil-pbc-proetale-operations`, the invertible sheaf counit in `lem-exc-proetale-closed-fully-faithful`, and the localized units/counits in `def-weil-exact-derived-adjunction`. I opened all three statements: the last explicitly specifies the localized adjunction, rather than merely defining the phrase “exact”. The closed functor's exactness is already a hypothesis of the item; the quasi-compact complement is present. Exact inverse image uses the identified constant coefficients. Localizing the degreewise inverse of the counit gives its derived inverse. The Hom bijection then proves derived full faithfulness in a few lines. This avoids treating sheaf full faithfulness alone as derived full faithfulness.

Step 2 uses exactly the derived support adjunction asserted in `lem-pur-support-localization-triangle`, on these same ordinary bounded below categories. Its counit and the full faithfulness from step 1 make postcomposition with the counit bijective on the relevant Hom set. This is a direct composition of two Hom bijections, not an uncited uniqueness theorem. The finite commutative ring and quasi-compact complementary open match that node's hypotheses. No noetherianity or etale-origin assumption is added.

Step 3 cites `def-weil-triangulated-category`, whose actual statement contains both signed rotation and completion of the commuting square. The two identity maps commute because both second arrows are the prescribed open unit. I checked the minus sign: the rotated last arrows are minus the shifted first arrows, so the TR3 equation gives epsilon[1] times t equals a[1]. Unshifting gives epsilon times c equals a. Its other equation is precisely c[1] times b equals the support boundary, proving the missing square. The short rotation argument is elementary from the cited axioms, rather than a separate lemma.

Step 4 invokes the full statement of `lem-sf-triangle-morphism-iso`, with two identity components; its conclusion makes the first component invertible. The inverse is lifted through derived full faithfulness and the two inverse identities are checked using faithfulness. The node `def-weil-pbc-triangles-with-shift` explicitly says that componentwise isomorphisms give an isomorphism of triangles. No unsupported assertion that an objectwise isomorphism preserves boundaries remains.

Step 5 uses the natural support adjunction from the support-localization node. The displayed equation applies its actual counit naturality, with u on L and v on K. Injectivity of the Hom bijection proved in step 2 gives the naturality equation for theta. Arbitrary completions have the same first component by the same injectivity, so their choice disappears. No uniqueness of arbitrary cones is asserted.

I checked B–E against these files: no new statement-only nodes, hidden sublemmas, hollow constructions, relabelled clauses, unlogged searches, or changes to other nodes. Every cited statement has a verbatim excerpt in `citations.json`; each cited node was opened. A read-only dependency traversal found no path from these ingredients back to this item. Every step is under 2000 characters. Small cases checked are the empty closed complement (both supported terms are zero), the empty open complement (the open term is zero and a is invertible), K=0, and L=0. The equations and isomorphism conclusion agree in each case, including the boundary signs. There was no earlier sandbox split or report to repair; the substantive correction to the initially contemplated argument was to supply derived full faithfulness before identifying the TR3 completion with the transpose.

Dry-run citation repair: expanded the step-3 excerpt to quote the complete TR2 and TR3 clauses; the original short clause was verbatim but below the gate's minimum excerpt length. The proof and statement did not change.
