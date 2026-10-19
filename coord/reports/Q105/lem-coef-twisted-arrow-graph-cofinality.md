# Q105 stage-1 split: lem-coef-twisted-arrow-graph-cofinality

## 1. Files written

- `dag/nodes/sec-six-functors/lem-coef-twisted-arrow-graph-cofinality.json`: existing statement, now split in nine steps. Its statement and inherited provenance/searches are preserved.
- `dag/nodes/sec-six-functors/lem-coef-left-fibration-fiberwise-coinitiality.json`: new statement-only node, unsplit; no Mathlib match. This is Cisinski's general fiberwise theorem for maps of left fibrations over products, expressed by restriction on coherent cocone spaces.
- `citations.json`: one verbatim statement quotation for each of the item's seventeen step citations. Where a step uses several clauses I quoted the complete statement, rather than an excerpt that concealed a missing clause.
- `report.md`: this report. `searches.jsonl` was written by the required search command; `write_split.py` is the item-specific reproducible sandbox editing script.

One new node; zero Mathlib leaves. No Lean, unit, coordinator, launcher, live-project, or repository file was written. No compiler, Lake, library build, local preflight, or local DAG-review command was run.

## 2. Attachments

None. The item's slopmaster2 audit is `none`. Searches for the exact blueprint id, twisted-arrow/edgewise terminology, left fibrations, and fiberwise coinitiality in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` returned no declaration stating the item or the new lemma. The upstream master checkout is reference material and was not treated as proof evidence.

## 3. Wanted sources

WANTED: Denis-Charles Cisinski, *Higher Categories and Homotopical Algebra*, July 30 2026 revision, https://cisinski.app.uni-regensburg.de/CatLR.pdf, Definition 4.4.13, Proposition 4.3.3, Section 5.6 (especially Lemma 5.6.7 and Proposition 5.6.9) and Theorem 6.4.5, for this item and its new fiberwise theorem. Read online; no archival copy was found in `literature/`.

WANTED: Jacob Lurie, *Higher Topos Theory*, https://www.math.ias.edu/~lurie/papers/HTT.pdf, Propositions 4.1.1.7–4.1.1.8, for the cocone-space form of the new generic theorem. Read online at printed pp. 226–227 (PDF p. 243). No matching Stacks tag states either quasicategorical theorem. These are precise alternative literature citations, not invented Stacks tags.

## 4. Audit findings and corrections

The item statement is sound and unchanged. Cisinski calls a map cofinal when its opposite is final (Definition 4.4.13, printed p.160); copying the word without checking this would give the wrong variance. His second canonical map (5.6.8.2) is exactly this item's graph map. I used that map, not the first canonical map, and explicitly swapped product factors to put the fixed target in the common factor of Lemma 5.6.7.

The current blueprint ancestor is `prop-coef-integral-exceptional-adjoint`, main-20261015 order 2493 under `sk-thm-sf-package`. Its current text states the derived adjunction, reductions, and units/counits, with no separate twisted-arrow proof. The item's inherited ancestry refers to the older proof paragraph 2 and its rectification foundation. I preserved the historical ancestry and the maintainer-owned unit binding `sk-prop-sf-biduality-general`, read that unit and the six-functors chapter, and explained in `split_report.blueprint` how this foundational split serves the same adjunction. This item is not a key statement of the unit, so there is no unit realization edit.

Several tempting existing tools cannot be cited here: `lem-coef-infinity-cofinality-space-test`, `lem-coef-infinity-cofinal-comma-criterion`, `lem-coef-space-transport-classification`, `lem-coef-coherent-nerve-comparison`, and `lem-coef-enriched-hom-twisted-arrow-comparison` each already have a dependency path to this item. For example the cofinality test reaches transport classification, model-nerve localization, local adjoints, interval adjunctions, adjunction mapping equivalences, Hom-bifunctor functoriality, and this item. I avoided these nodes and used the independent slice statements, normalized final-index colimits, and generic coherent-cone calculus instead. The new lemma has only foundational definition dependencies.

The actual comparison on cocone spaces is proved, not just a comparison of chosen colimit objects. In particular Step 6 uses evaluation at the final identity vertex and checks that restriction commutes with that evaluation. Step 8 then uses the specified cocone and every test object to obtain the if-and-only-if clause with the same vertex.

Naturality in a noncartesian commutative square does not mean that the resulting map of total left fibrations is a pullback equivalence. Step 9 factors the map through the pullback of the target left fibration; straightening then gives a transformation over the common base. This records the correct comparison for arbitrary commutative squares.

## 5. Outstanding work

The new general fiberwise theorem is deliberately statement-only, for a future one-level split. It is not an omitted step of this item's proof: the item proves all of its special fiber hypotheses. Its source proof reduces to covariant weak equivalences using slices over the other product factor; that is the separate argument the generic node must later formalize. The item's proof origin is `agent` because its online sources are not archived locally.

## Not duplicates

lem-coef-left-fibration-fiberwise-coinitiality vs lem-coef-twisted-arrow-graph-cofinality: the new lemma concerns arbitrary maps of left fibrations over two products with a common factor and assumes strong coinitiality of every fiber map. It constructs no graph, twisted arrows, classifier, or slice comparisons; the item must verify the left-fibration square and prove the fiber hypothesis. It does not restate the item or any unconditional clause of it.

lem-coef-left-fibration-fiberwise-coinitiality vs lem-coef-infinity-cofinality-space-test: the latter detects finality using space colimits or comma categories; it has no theorem passing from common-factor fibers of left fibrations to their total categories.

lem-coef-left-fibration-fiberwise-coinitiality vs lem-coef-infinity-cofinal-comma-criterion: the latter assumes contractible comma categories for the total functor; it supplies no fiberwise left-fibration criterion.

lem-coef-left-fibration-fiberwise-coinitiality vs lem-coef-cartesian-terminal-twisted-resolution: the latter is a construction for cartesian fibrations over ordinary nerves with terminal fibers; the new lemma concerns arbitrary quasicategory products and left fibrations, with an already given map and fiberwise coinitiality assumption.

lem-coef-left-fibration-fiberwise-coinitiality vs lem-coef-cocartesian-categorical-base-change: the latter pulls a categorical equivalence back along a cocartesian fibration. Coinitial maps need not be categorical equivalences, and the new lemma proves a different total-map criterion.

Whole-DAG and blueprint searches used `twisted`, `cofinal`, `coinitial`, `fibrewise`, `left fibration`, and `5.6.7`, plus source-place/key-term searches. No existing node states the new lemma; there is no shared Stacks tag requiring further pair comparisons. Ordinary Mathlib category-of-elements and ordinary final-functor results do not state its quasicategorical version.

## Review by Q105

I read the item against Cisinski Section 5.6, including the actual two squares in paragraph 5.6.8 and the proof on printed p.242. I read the new lemma against Lemma 5.6.7, printed pp.240–241, rather than extrapolating a fiberwise assertion for arbitrary maps. Both vertical maps in that lemma must be left fibrations over products: Steps 1 and 4 verify exactly those hypotheses. I also read Definition 4.4.13, Proposition 4.3.3, Theorem 6.4.5, and HTT Propositions 4.1.1.7–4.1.1.8 to check the opposite-final convention and the actual restriction comparison, including arbitrary target categories without completeness hypotheses.

For Step 1 I opened `lem-coef-twisted-arrow-left-fibration`, `def-coef-infinity-fibrations`, and `def-cbc-enhanced-diagrams-cones`. They respectively state the twisted-arrow left fibration, define its full horn range, and define the quasicategories/products/pullbacks used. Pullback stability and the inner-horn argument are written out; no additional fibration theorem is smuggled in.

For Step 2 I reread `lem-coef-space-valued-straightening`, the target-fixed collapse clause of `lem-coef-twisted-arrow-left-fibration`, and the final transport paragraph of `lem-coef-right-fibration-section-limit`. Straightening supplies a coherent classifier natural under base pullback, the collapse identifies its fixed-target restriction with the opposite join slice, and the transport lemma identifies this slice's coherent transport with the right-pinched mapping spaces, with precomposition. The join-simplex formula in the step supplies the other variable and its higher coherences; this does not cite a mere pointwise fiber equality as if it were a bifunctor comparison.

For Step 3 the cited twisted-arrow construction really gives the join-operator definition used. The proof writes the pullback coordinates and checks their equality and all operators. Step 4 uses only the fibration definition and the already constructed map; the chosen common factor is the target `A`, and its strict fibers are the correct fixed-target twisted-arrow fibers, not source fibers.

For Step 5 I opened the slice-equivalence-final statement, which applies to the identity edge without assuming the base object is final. I also reread the mapping-space-equivalence clause of `lem-cbc-enhanced-functor-cone-calculus` and the identity-preserving/naturality clauses of the twisted-arrow slice comparison. They imply exactly the needed finality of the opposite fibers and preservation of their identity vertices. No claim that `f` itself preserves final objects of `A` or `B` is used.

For Step 6 I checked the normalized identity-component clause in `lem-coef-infinity-final-index-colimit` and the dual cocone criterion in the cone-calculus node. The argument identifies evaluation with the inverse universal comparison and verifies its commutation with restriction. Thus it proves the entire fiber cocone-space hypothesis of the new lemma, for every diagram and test object. Step 7 uses the new lemma's actual stated restriction equivalence, and all its hypotheses were verified in Steps 1, 4, and 6. Step 8 uses the cone-calculus criterion for the specified cocone and checks the square for every test object; no colimit-existence theorem for a large indexing category is assumed.

For Step 9 I checked the strict degreewise naturality equations and the factorization through a base pullback. The straightening statement supplies exactly the base-change compatibility used there. Size is computed from `Tw(A)_n = A_{2n+1}` after identifying the finite ordered join; no `U`-smallness of `B` is required. Every other construction uses the larger universe `V` where both input quasicategories are small, and the space-valued classifier lives in a further ambient universe. The only off-unit proof tool is the generic coherent-functor/cocone calculus; it is declared in `split_report.tool_uses`.

I checked delivery-errors B–E against the files: the new node is self-contained and statement-only, introduces all objects and its exact hypothesis, uses ordinary TeX once, supplies a precise source rather than a section-number-as-meaning, and records only searches actually run by `msearch.py`. Loogle returned no LeftFibration/Initial hit; both semantic phrasings returned abstract model-category or ordinary-category statements. I read those signatures and inspected the relevant ordinary category and Kan-Quillen source files, so none is a leaf. All inherited item searches were retained, not fabricated or rerun unnecessarily. Every proof citation was opened and is quoted verbatim in `citations.json`.

Small cases: if `A` is empty, both `Tw(A)` and `W_f` are empty and restriction is the identity on the same empty-diagram cocone space; if `B` is empty a functor forces `A` empty. If `f` is the identity, the pullback and graph map identify with `Tw(A)` and its identity. If `A` is a point mapping to `1` in the ordinary interval `0 -> 1`, `W_f` has arrows `id_1 -> (0 -> 1)`; the graph selects its initial object, so its opposite selects the final object. This detects the variance error one would make by asserting that the graph itself is final. For the new lemma, an empty common factor forces both total spaces empty; for a one-point common factor it reduces to its own fiber hypothesis; for product left fibrations with discrete fibers over a point, coinitiality forces the corresponding bijection, consistent with the conclusion. I found no false statement and no need for a statement dispute.

Required final validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q105 lem-coef-twisted-arrow-graph-cofinality --no-push`. The delivery tool records its acceptance receipt in the sandbox; READY is reported only after it prints OK. This sandbox is for the independent second reader and will not be pushed by this worker.

## Second reading by Q105

- Item statement: checked against Cisinski Definition 4.4.13, Proposition 5.6.9 and diagram (5.6.8.2), including the opposite-final convention, both product factors, the cocone-space formulation, naturality, and the smallness clause; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against Cisinski Proposition 5.6.2 and the definitions of left fibrations, quasicategories, products, and pullbacks; the pullback lifting and total-space horn arguments supply the stated hypotheses; verdict: sound and elementary.
- Step 2: checked against Cisinski Propositions 5.6.2, 5.6.5, 5.6.13, Corollary 5.6.14, Remark 5.6.15, and the cited straightening and right-fibration transport statements; the classifier is identified coherently in both variables, with the correct precomposition direction; verdict: sound.
- Step 3: checked against the explicit second canonical map (5.6.8.2), degreewise join formula, and the twisted-arrow definition; the pullback coordinates and vertex triple are correct; verdict: sound and elementary.
- Step 4: checked against Lemma 5.6.7 after swapping factors, with $Z=\mathcal A$, $C=\mathcal A^{\mathrm{op}}$, $D=\mathcal B^{\mathrm{op}}$; the fixed-target fibers and square equation have the required orientation; verdict: sound and elementary.
- Step 5: checked against Proposition 5.6.5, the target-fixed slice equivalences, and the final-object characterization of equivalence arrows; identity vertices and opposites are handled correctly; verdict: sound.
- Step 6: checked against the normalized final-index colimit statement and the dual coherent-cocone mapping-space criterion; evaluation at the identity vertex commutes with restriction, giving the full fiber comparison; verdict: sound.
- Step 7: checked against the exact statement of the new fiberwise coinitiality node and all hypotheses established in Steps 1, 4, and 6; it yields precisely the displayed total restriction equivalence; verdict: sound.
- Step 8: checked against the coherent cocone criterion and the restriction square for every test object; the same cocone vertex is preserved; verdict: sound and elementary.
- Step 9: checked against Cisinski paragraph 5.6.8, straightening naturality, and the degreewise join-size calculation; strict naturality, pullback factorization, higher coherences, and universe bounds are all stated; verdict: sound and elementary.
- New node `lem-coef-left-fibration-fiberwise-coinitiality`: checked against Cisinski Lemma 5.6.7 and the finality/cocone-space characterization, with all quasicategories, maps, fibers, universes, and quantifiers introduced; verdict: self-contained, statement-only, and not a duplicate or Mathlib match. Independent searches (LeanFinder, Loogle, and grep) returned no quasicategorical declaration.

No mathematical or dependency repair was required. I changed only this report by adding this second-reading record; node statements, proof steps, citations, and search records remain unchanged because each was verified against its cited source and dependency statement. The staged delivery marker was not used as proof evidence. Small-case checks covered empty $\mathcal A$ or common factor, identity $f$, a point, and the ordinary interval $0\to1$, including the variance-sensitive graph orientation.
