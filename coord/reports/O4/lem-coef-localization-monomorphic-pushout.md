# Stage-1 worker report

1. Files written:
   - `dag/nodes/sec-six-functors/lem-coef-localization-monomorphic-pushout.json`: repaired item split; statement and first three proof steps retained, final 2043-character step divided into three short steps.
   - `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-of-cospan-limits.json`: new statement-only lemma; Mathlib searches found no exact coherent infinity-categorical match.
   - `dag/nodes/sec-six-functors/lem-coef-infinity-test-equivalence-by-functor-cores.json`: new statement-only lemma; Mathlib searches found no exact coherent infinity-categorical match.
   - `citations.json`: verbatim statement quotations for every node cited by every item proof step.

2. Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the designated upstream reference for the item id, the Lean declaration name, the Kerodon tags, and localization/pushout terms. No finished declaration of this item or either new lemma was found there. The existing shared `lean/` metadata is a later stage-2 record, not evidence available in the designated source checkout; I did not treat it as an attachment.

3. WANTED:
   - archived Kerodon Proposition 6.3.5.3 (tag 01N7), implication (1) to (2), for the item and the cospan-limit comparison;
   - archived Kerodon Example 4.5.5.12 (tag 01FJ), for the degreewise-monomorphic pushout identification used in Step 1;
   - archived Kerodon Proposition 6.3.1.13 / the corresponding mapping-space universal-property passage, for the all-test-core equivalence criterion. These sources were read as the online Kerodon references recorded in the inherited item metadata; no source was downloaded or placed in the repository.

4. What was wrong and what I corrected: the inherited item proof's final step was 2043 characters and compressed several independent arguments: strict compatibility of the three restriction functors, transport of a limiting cospan through component equivalences, and detection of a functor equivalence by all test quasicategories. I kept the mathematical route and conclusion unchanged, made the strict cospan map a separate step, and added two smaller statement-only nodes for the hidden limit-apex comparison and the all-test-core criterion. The new nodes are strictly smaller than the item and carry statements only, as required. The item still uses only the two degreewise-injective legs; no injectivity of the other span legs or of the localization maps was introduced. The pushout edge union and all localization hypotheses remain unchanged.

## Not duplicates

lem-coef-infinity-equivalence-of-cospan-limits vs lem-coef-infinity-terminal-pullback-criterion: the existing node gives the mapping-space criterion and invariance of limiting criteria under cospan equivalences; the new node packages the resulting apex-map equivalence for a specified map of two limiting cones.

lem-coef-infinity-equivalence-of-cospan-limits vs lem-coef-infinity-isofibration-pullback-limit: the existing node treats strict simplicial pullbacks along an isofibration; the new node concerns an objectwise-equivalent pair of cospans and their limiting cone apices.

lem-coef-infinity-test-equivalence-by-functor-cores vs lem-coef-infinity-full-essential-image: the existing node assumes full faithfulness and identifies a prescribed full essential image; the new node assumes equivalences on all core functor-category tests and concludes that the original functor is an equivalence.

lem-coef-infinity-test-equivalence-by-functor-cores vs lem-coef-infinity-pointwise-yoneda-evaluation: the existing node is an evaluation equivalence for representable presheaves; the new node is a global test-object criterion for a functor between quasicategories.

lem-coef-infinity-equivalence-of-cospan-limits vs lem-coef-localization-monomorphic-pushout: the new node is the abstract apex-equivalence consequence for any two limiting cospan cones, while the item proves a localization statement for a particular simplicial pushout and supplies the cospans and localization data.

lem-coef-infinity-test-equivalence-by-functor-cores vs lem-coef-localization-monomorphic-pushout: the new node is the general all-test functor-equivalence criterion, while the item applies it after constructing localized functor-category pullbacks and concludes the specific edge-localization universal property.

lem-coef-localization-monomorphic-pushout vs lem-coef-universal-localization-pushout: the item is the specified-edge localization gluing theorem for two spans; the existing node is a different universally-localizing base-change statement and depends on the item's route, so it cannot replace either new helper.

5. What I could not finish: no Lean was written or compiled because this is stage 1 and the human explicitly forbids compiler/Lake work. The two new nodes remain unsplit statement-only leaves for later workers. No shared repository or live project file was modified.

## Review by N4

I read the complete inherited item node, `dag/units/sk-prop-sf-biduality-general.json`, `dag/chapters/sec-six-functors.json`, `coord/repair-notes/lem-coef-localization-monomorphic-pushout.json`, the worker contract, and the Kerodon 01N7/01FJ route recorded in the inherited source and reports. I also opened every cited DAG statement used by the seven proof steps. Steps 1--3 were left mathematically unchanged: Step 1 identifies strict functor-category pullbacks and uses the restriction-isofibration and pullback-limit statements; Step 2 uses the two edge-image inclusions, pointwise equivalences, and mapping-composition cancellation to prove the localized restriction map is an isofibration; Step 3 identifies the full subcategory inverting the image union with the pullback of the three full subcategories. The hypotheses checked in these steps are exactly degreewise injectivity of `u_0` and `v_0`, the two edge inclusions, and the three localization equivalences.

For repaired Step 4 I checked the strict equations `p ∘ j_i = k_i ∘ p_i` and `(G p_0)u_0 = (G v_0)p_{01}` (and the analogous equation for index 1), so the component precomposition maps really form a cospan map. The localization definition supplies each component functor equivalence, and `lem-coef-infinity-pointwise-equivalences` supplies the equivalence of the cospan diagram. Repaired Step 5 applies the new cospan-limit node only after Step 1 has supplied the limiting cone and Step 3 has supplied the limiting localized cone; the existing terminal-pullback criterion supplies the natural mapping-space comparisons and cospan invariance. Repaired Step 6 applies the new all-test-core node to those comparisons, then unfolds the definition of localization; the edge set `W = j_0(V_0) ∪ j_1(V_1)` is independent of the test quasicategory.

For each new node I checked that its statement introduces all objects and hypotheses, is strictly smaller than the item, and has no proof steps or hollow data. The cospan-limit node says precisely that a compatible map between two limiting cones over an objectwise-equivalent cospan has an equivalence as apex map, with the equivalent core mapping-space formulation. The test-core node says precisely that equivalences on `Fun(Q,-)^≃` for every small quasicategory detect a functor equivalence. I searched the whole DAG and blueprint for both statements and found no exact or more general existing node; the closest existing nodes state the mapping-space criterion, strict isofibration pullback, full essential-image construction, or representable Yoneda evaluation, each with different hypotheses or conclusions. I tested the repaired route on empty overlap, empty edge collections, identity vertical maps, disjoint pushouts, a terminal test category, and a noninjective second span leg; no hidden nonemptiness or injectivity assumption appears. The Mathlib search log contains the required LeanFinder, Loogle, grep, and LeanSearch queries for the item and both new nodes; all hits are ordinary category/ring localization or pushout facts and none matches these coherent infinity-categorical statements.
