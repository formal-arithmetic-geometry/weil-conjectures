# Q33 stage-1 report: thm-sf-hom-comparison-constructible

## Files written

- `dag/nodes/sec-six-functors/thm-sf-hom-comparison-constructible.json`: existing item, split into eight proof steps; no new nodes.
- `citations.json`: 31 verbatim statement citations, one for every cited node in every step.
- `report.md`: this worker report.

## Attachments

None. The source declaration `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom` in `WeilConjectures/SixFunctors/ProEtale/Derived/HomComparison.lean:126-141` has a `sorry` proof and concludes only `Nonempty (...)`; it does not provide the canonical comparison arrow in the item. The source search found no sorry-free declaration with the item's statement.

## WANTED

None.

## Not duplicates

No new nodes were created, so no duplicate-node comparison is applicable. Every proof dependency was an existing DAG node whose statement was read.

## What was checked and corrected

The item statement was compared with the blueprint node (master order 2198) and with the current `main-20261015` blueprint copy. It was not weakened: it retains finite type over the algebraic closure, the etale-to-pro-etale comparison, the finite-Tor constructible first input, the bounded constructible second input, and the canonical internal-Hom comparison. The source Lean theorem was checked separately and rejected as an attachment because its proof is `sorry` and its result is only an existential isomorphism.

The imported proof's fifth step was 2038 characters and combined construction of the evaluation transpose with its compatibility under restriction. I split it into steps 5 and 6, each below 2000 characters, while retaining the same route and dependencies. I also marked all eight steps non-elementary whenever they invoke a named DAG lemma; the earlier `elementary: true` labels for the Hom-complex and adjunction calculations did not meet the brief's one-line criterion.

## Review by Q33

I read the item node, the unit `dag/units/sk-thm-sf-hom-ctf.json`, the chapter record, the master blueprint proof, the current blueprint copy, and the source file `WeilConjectures/SixFunctors/ProEtale/Derived/HomComparison.lean`. I opened the statement of every one of the 23 distinct cited DAG nodes and recorded its verbatim full statement in `citations.json`; the 31 step-node pairs all pass the normalized substring check.

Step 1 uses the finite affine-open-cover statement, the locally-finite-type affine-pairs criterion, the definition of finite type over a field, and affine-source-separatedness. These statements justify a finite affine cover by charts of finite type whose structure maps are separated. I checked that the item supplies quasi-compactness and locally finite type, and that no claim about affine intersections is used.

Step 2 uses localization, exact restriction with its extension-by-zero adjunction, the definition of bounded constructibility, the flat-model characterization of finite Tor amplitude on the etale site, and flatness after slice restriction. These statements justify restriction of both inputs, preservation of cohomological bounds and constructible stratifications, and the restricted bounded flat model for the first input. No finite-Tor hypothesis is silently imposed on the second input.

Step 3 uses the derived-internal-Hom definition, restriction of K-injectives, sheaf Hom, localization, and the Hom-complex definition. They give the termwise identification of restricted Hom complexes, including the differential, and hence the displayed derived-Hom restriction isomorphism. This is a model calculation, not a stalk formula.

Step 4 uses the explicit site-comparison adjunction, localization, exactness of comparison pullback, and exact restriction. The direct-image formulas give `nu_X,* j_proet,* = j_et,* nu_U,*`; the two left adjoints therefore have the same Hom bijections. Exactness then transports the identification to complexes and derived categories. I checked that this step uses the actual comparison morphism node, not a proof detail absent from its statement.

Step 5 uses the derived tensor-pullback comparison, exact comparison pullback, K-flat resolutions, and the derived-internal-Hom definition. These statements construct the evaluation-defined transpose of the canonical comparison map with the displayed tensor comparison, on valid K-flat/K-injective representatives.

Step 6 uses complex currying, the K-flat-to-K-injective Hom lemma, global-sections detection of derived Hom, exact restriction, K-injective restriction, and exact comparison pullback. Their functoriality makes currying, evaluation, units, and counits agree after restriction, so the map from step 5 restricts to precisely the canonical map on each affine chart. The pure-tensor check `f ⊗ x ↦ f(x)` is written explicitly.

Step 7 uses the separated finite-type site-comparison theorem. Step 1 supplies separated finite-type charts and step 2 supplies its two input hypotheses; its statement gives the evaluation-defined comparison isomorphism on each chart for the same finite coefficient stage and `ell != p` convention.

Step 8 uses exact restriction and the unbounded derived isomorphism criterion. Applying cohomology, gluing the local inverses on the pro-etale cover, and then detecting isomorphisms by all cohomology sheaves proves the global comparison. The empty scheme is explicitly included. I checked the point case, zero inputs, and empty-cover edge cases while auditing the locality argument.

No statement was corrected, no new node was needed, no Mathlib leaf was claimed, and no SGA source was introduced. The only repair was the proof-step granularity and elementary classification described above.

## What could not be finished

Nothing remains for this stage-1 split.
