# Worker report: lem-weil-extension-by-zero-exact

## Files written

- Updated `dag/nodes/sec-smooth-purity/lem-weil-extension-by-zero-exact.json`.
- Added `citations.json` with the one citation used by the proof step.
- Added this `report.md`.
- New nodes: 0. Mathlib leaves: 0.

## Attachments

None. I searched the declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item identifier and for extension-by-zero/exactness. The declarations `AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek` and the nearby finite-colimit example establish generic categorical preservation, but they do not identify their functor with the explicit extension-by-zero functor on modules over the constant coefficient sheaves required by this item. The earlier proposed attachment was therefore rejected and is not repeated.

## WANTED

None. The node uses the canonical blueprint paths recorded in the imported item and in the cited existing node. The cited theorem and its Stacks references are present in the shared DAG; no additional literature was needed for this split.

## Not duplicates

- `lem-weil-extension-by-zero-exact` vs `lem-cbc-proetale-extension-zero`: the existing node is a stronger pro-etale module statement (exact left adjoint together with stalk, degreewise, and scalar-compatibility clauses), while this item is the narrower exactness clause in the six-operations unit; it is cited rather than recreated.

## Review by Q23

I read the imported item node, its unit record `dag/units/sk-def-sf-operations.json`, and its chapter record `dag/chapters/sec-smooth-purity.json`. I also read the complete statement and first proof step of `lem-cbc-proetale-extension-zero`, together with its source record. That statement has the same finite commutative ring and open-immersion hypotheses as this item and explicitly identifies the functor as the functor of `def-weil-extension-by-zero`. Its first clause says verbatim that this functor is the exact left adjoint of restriction, which is the exactness assertion needed here.

The only proof step uses that cited statement and nothing else. I checked that its hypotheses cover the constant coefficient sheaf and the finite-torsion specializations $A_{E,n}$ mentioned by the item. The proof of the cited node identifies the localized pro-etale site and constant coefficients before applying the exact module restriction/extension result, so no unsupported change of sites or coefficient category is imported into this specialization. The citation quote is a verbatim part of the cited node's statement, and `citations.json` records it. Since no new node was created, there are no additional C1/C4 node statements to audit; the one cross-unit use is declared in `split_report.tool_uses`.

I also read the definitions named by the item (`def-weil-extension-by-zero`, `def-weil-pbc-proetale-site`, `def-weil-finite-torsion-constructibility`, and `def-weil-scheme-morphism-properties`) while checking that the specialization preserves the stated functor and hypotheses. Edge cases $A=0$, $U=\varnothing$, the identity open immersion, and the finite-torsion rings $A_{E,n}$ are all covered by the cited universal exactness statement. The required Mathlib searches were run with the item id: no exact Mathlib declaration was found; the two LeanSearch calls were unavailable and are recorded as such. No Lean files or compiler/build tools were written or run.

## Unfinished work

None.


## Second reading by Q23

- Item statement: compared hypothesis by hypothesis with the blueprint source `sk-def-sf-operations/lem-weil-extension-by-zero-exact.md`: finite commutative ring, arbitrary open immersion of schemes, small pro-etale module categories over constant coefficients, the stated finite-torsion specializations, and exactness all agree. No statement correction is needed.
- Step 1: read the complete statement of `lem-weil-proetale-weakly-etale-localization`; its open-immersion case supplies the site equivalence including coverings, the constant coefficient ring identification, the module-category identification, and the zero-or-one-map property. Its hypotheses hold for the given open immersion and coefficient ring.
- Step 2: read the complete statement of `lem-pur-site-restriction-module-adjunction-exact` and `def-weil-extension-by-zero`, the direct-sum definition `def-weil-extension-by-zero-presheaf`, and Stacks `sites-modules.tex` Tags 03DI (`lemma-extension-by-zero`) and 03DJ (`lemma-extension-by-zero-exact`). The theorem concerns module sheaves, its ring sheaf is commutative here, and its functor is the module sheafification of the direct-sum presheaf. Step 1 reduces that formula, its action, and its restrictions to exactly the functor in the definition. Thus the exactness clause applies, with no appeal to a proof hidden inside a cited statement.
- New nodes: none; B1-B7 are vacuous. DAG searches by extension-by-zero keywords and the source tags located the existing module theorem and localization lemma in `sk-def-sf-operations`. They already supply the unit's own route, so the split needs no duplicate theorem and no cross-unit tool edge.
- Edge cases: for the zero coefficient ring every module is zero; for the empty open the source sheaf category and extension are zero; for the identity open every ambient object has its unique structure map and the presheaf is the original sheaf. Over a field and for a proper nonempty open, the same zero-or-one-summand formula applies without any separatedness or finiteness assumption on the schemes. The finite-torsion coefficient definition has n >= 1; n = 1 is covered, and there is no n = 0 hypothesis to add.
- Search and attachments: independently ran msearch LeanFinder for an exact left adjoint to localized module restriction, Loogle for `SheafOfModules.overFunctor`, and grep for `overFunctor|PreservesFiniteLimits.*pullback`; the raw results are in `searches.jsonl`. Read the returned Mathlib restriction definition and generic sheaf-pullback preservation instances: they do not identify this module extension-by-zero functor in one specialization. Read the slopmaster2 lower-shriek definition and finite-limit preservation instance; the generic sheaf-valued declaration does not by itself identify the constant-ring module-sheaf category, so no new attachment or Mathlib leaf is asserted.

Changes made: replaced the worker's valid but unnecessary cross-unit citation to `lem-cbc-proetale-extension-zero` by the two existing same-unit inputs above (C7); split the application into the site/coefficient identification and explicit presheaf/exactness application; regenerated verbatim statement quotes for every citation; updated proof dependencies, proof origin, and split report. The first worker's sections above are preserved. No new nodes, Lean edits, compiles, or changes to the shared repository were made.
