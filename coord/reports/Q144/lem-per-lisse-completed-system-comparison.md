# Stage-1 delivery: lem-per-lisse-completed-system-comparison

Group Q144; worker stage1; 2026-10-18. Direct delivery under the dispatcher's brief.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-lisse-completed-system-comparison.json`: item, statement, split into ten proof steps; no Mathlib match. Its statement is unchanged. Added the inverse-image and sheaf-tensor definition dependencies needed by the pullback/scalar-extension clause.
- `citations.json`: one entry for every proof-step citation, with an exact substring of the cited statement.
- `report.md`: this report. Search receipts are in `searches.jsonl`; the local source extract and writing script are sandbox research artifacts.

New nodes: **0**. New Mathlib leaves: **0**. No unit file is changed: this item is a coefficient-comparison tool beneath the smooth-pullback node, not the key statement of `sk-p-dl-a1-perverse`.

## Attachments

None. Searched all project declarations in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id and completed/lisse/system terminology. The hits in `EtaleCohomology/Purity/RealSheaves/LocalSystems.lean` concern representation-theoretic dictionaries and lattices, while the `SixFunctors/ProEtale/Adic/` material concerns another coefficient presentation. Neither states this integral completed-coefficient equivalence together with the raw rational Hom comparison and its naturality. No upstream master sorry is treated as a proof.

## WANTED

None. The sources used are present locally.

## What needed repair

The item was statement-only, with empty proof and dependency lists for the proof. It already distinguished raw rationalization from all rational lisse modules; I preserved that distinction. In particular the proof does not strengthen full faithfulness to global essential surjectivity, and does not invoke the separate etale-local lattice theorem.

I reused `lem-sfb-integral-lisse-reduction-equivalence` for actual completed-coefficient reconstruction. Creating another effectivity node would duplicate it and would move the item's first clause into a new node. Finite etale/pro-etale descent is supplied by the stronger existing `det-pe-finite-local-systems-twist`; unlike a bare origin statement, it supplies full faithfulness and a quasi-inverse, which are necessary to descend the transitions. For rational Hom, I used the actual qcqs continuity statement `det-pe-bounded-continuity-sections`, rather than assuming that local denominators have a global bound.

The inherited searches are retained. Six new queries were made only through `msearch.py`; their literal queries, actual hit summaries and verdicts are appended to the item. Both semantic phrasings were read. I inspected `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` (especially lines 59–79) and `Mathlib/Condensed/Discrete/Module.lean` (lines 137–152 and 254–269). The former defines the coefficient sheaf and its cohomology; the latter proves discrete-module embedding full faithfulness. Neither proves this item's tower equivalence or rational Hom theorem. Loogle returned no hits; both LeanFinder calls and LeanSearch were available. No service failure is counted as an absence result.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs. Whole-DAG concept/source searches found the existing integral reconstruction, finite-local-system descent, Hom/limit definitions, continuity, and comparison-pullback results that the proof now cites. The whole-blueprint searches for lisse, normalized inverse systems, finite local systems and rational full faithfulness found no blueprint node stating all of this item's comparison with these hypotheses and clauses. The `blueprint.same_as` field remains the searched empty list; the inherited ancestry and precise `from.place` are retained.

## Review by Q144

I read the chapter record `sec-deligne-laumon-a1`, the unit `sk-p-dl-a1-perverse`, the ancestor's statement and first support/pullback proof paragraph in the current `main-20261015` blueprint, and the item's current repository statement. This comparison supports the local-system models used below that support argument; it does not replace the curve Fourier route or any purity theorem. For the mathematical source I read Bhatt–Scholze Corollary 5.1.5 (p.35), Lemma 6.8.2 and Definition 6.8.3 (pp.58–59), and all clauses and the proof of Proposition 6.8.4 (pp.59–60). Its integral proof is omitted in the paper, so I read and reuse the existing DAG reconstruction statement, whose split supplies that missing compatible-basis argument. I also read Stacks Tag 099Y (`proetale.tex`, `lemma-compare-locally-constant`), including its preservation of the constant module model, and the sheaf-tensor construction and Tag 03CZ in `sites-modules.tex`. There are no new nodes needing independent source checks.

For step 1 I opened the complete statement of `lem-sfb-integral-lisse-reduction-equivalence`: it expressly identifies the continuous-function ring, its inverse limit, its finite quotients, and its localization. The coefficient-extension definition supplies the valuation/uniformizer convention. Hence the argument compares the completed coefficient sheaf in this item, not the generally different constant A sheaf. Inverting ell or varpi is the same because ell is a unit times a positive power of varpi.

For step 2 the statement of `det-pe-finite-local-systems-twist` gives an equivalence, not just essential surjectivity, for finitely presented local systems; finite modules over the finite ring A_n are explicitly included. Its descent does not by itself assert that an arbitrary model is free. I supplied the short extra argument on a nonempty common trivializing object, citing the exact constant-module stalk statement `lem-weil-proetale-constant-sheaf-stalk`, to identify the descended model with A_n^r. This treats zero rank and disregards empty charts correctly.

For step 3 the inverse-image/tensor lemma really asserts preservation of colimits and tensor; its hypotheses hold for the comparison geometric morphism defined in the item's dependencies. The balanced coequalizer gives the relative tensor comparison. Transition maps are descended in the A_{n+1}-module local-system category, where the A_n-module target is finite but need not be free as an A_{n+1}-module. This is why the general finite-module descent node is used. The normalization isomorphism is reflected by its equivalence. Uniqueness descends the equations, rather than merely choosing unrelated finite-level models.

For step 4 the reconstruction node's statement provides exactly the natural unit, counit and limit functor used here. The module-limit node says limits are sectionwise, so the coefficient action and projections are the actual ones. Normalization makes the free ranks agree modulo the residue field. The finite-cardinality argument uses q>1, which holds for the residue field of a nonzero DVR; it includes r=0. No connectedness or global chosen basis is assumed.

For step 5 I checked the complete definition of `def-pur-sheaf-hom`, including the global-section Hom identification, and `lem-weil-pbc-module-sheaves-colimits-forgetful` for the actual localization colimit. On common local bases the comparison is the finite matrix localization map; finitely many local fractions admit a common exponent, and the map is the canonical scalar-extension map, so its inverses glue. This is a coordinate calculation from definitions and is marked elementary, with no unstated internal-Hom base-change theorem.

For step 6 I read the complete statement of `det-pe-bounded-continuity-sections` and checked all its hypotheses: the terminal object X is qcqs (Noetherian), the index is the small filtered natural-number category, the complexes are degree zero and uniformly vanish below 0, and q=0 identifies hypercohomology with sections. The colimit cocone is multiplication by varpi. Thus this theorem supplies a global denominator bound on Hom; local fraction representatives alone would not do so. The raw rational category in `def-pod-lisse-l-adic-sheaves` has precisely Hom tensor E, and the proof displays that functor's Hom map.

For step 7 I checked both the underlying sheaf inverse-image definition and the general finite-limit/tensor preservation statement. Completed-coefficient module pullback is explicitly constructed with the residue-induced map f^{-1}B_X -> B_Y; no claim that this ring map is an isomorphism is made. The statement of `lem-weil-pbc-comparison-pullback` gives the finite etale/pro-etale comparison and its identity/composition equations. The inverse-limit comparison is induced by the projections and proved invertible on a pulled-back compatible basis. It does not assert that inverse image preserves arbitrary inverse limits, and does not require f to be smooth, etale, proper, or finite type.

For step 8 I checked the scalar-extension clause of `def-pod-lisse-l-adic-sheaves` in full: the source level is ceil(m/e), not m in a ramified extension. The displayed map is well-defined by the quotient coefficient map, respects tower transitions by reduction of each factor, and is an isomorphism on the finite-free local basis. Tensor and the finite-level comparison justify every identification. No finite-quotient flatness hypothesis is silently used.

For step 9 I checked that the two comparison nodes actually assert identity/composition for the maps being used. I then wrote the coefficient products on local pure tensors for pullback composition, coefficient-extension composition, their mixed square, and units. These are balanced section maps, hence maps after sheafification. The inverse-limit equations follow by composing with each projection. This replaces an unsupported assertion that coherence is automatic. In a coefficient tower one can take a common large source quotient, so the calculation is independent of a chosen cofinal indexing formula.

For step 10 the scalar-extension and fraction formulas show that the rational functor is the one of step 6, including on morphisms. In a ramified extension the image of varpi is invertible in E', so the same fractions and equations remain valid. Local bases prove invertibility of the rational comparisons. I checked empty X, zero modules, varying finite ranks, identity f, a composite f, the identity coefficient extension, a ramified extension (e>1), and two successive coefficient extensions. All reduce to the displayed formulas. No counterexample or statement correction was needed.

Every use was checked against the cited node's statement, and `citations.json` contains a verbatim relevant substring for all 23 uses. All proof steps have fewer than 2000 characters; the finite-free Hom and coefficient-extension calculations are routine coordinate arguments, while the non-elementary reconstruction, descent and global continuity facts remain explicit cited nodes. I checked delivery-errors B–E: no new unsplit proof sketches, no duplicated nodes, no substituted item clauses, no invented Mathlib receipts, no added hypotheses, no assumed global lattice, no inverse-limit/pullback interchange without its local proof, and no dependence on an SGA source.

## Tool uses outside the unit

The seven statement-node tools declared in `split_report.tool_uses` are coefficient reconstruction, finite etale/pro-etale descent, the constant-module stalk, general inverse-image tensor preservation, general module limits/colimits, qcqs sections continuity, and comparison-pullback compatibility. These supply generic coefficient/topos facts needed under the ancestor's support argument. The Fourier/perversity unit supplies none of these independently. They do not replace any step of that unit's route.

## Unfinished work

None in this one-level split. The existing dependency nodes retain their own completion states; they were not edited. Server dry-run and delivery results follow below.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q144/lem-per-lisse-completed-system-comparison at 8172ad3924: preflight passed`. A separate read-only consistency check confirmed that the statement is unchanged, proof dependencies are exactly the union of step uses, every cited node exists and is unmerged, and all 23 citation quotes match the current repository statements.
