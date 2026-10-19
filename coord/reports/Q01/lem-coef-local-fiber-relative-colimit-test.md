# Worker report

Item: `lem-coef-local-fiber-relative-colimit-test`. Group Q01. Stage 1 only, 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-local-fiber-relative-colimit-test.json`: existing item, statement and statement dependencies retained; six proof steps added, status set to `split`; no Mathlib match.
- `citations.json`: nine verbatim `(step, node)` quotations covering every proof citation.
- `report.md`: this report.
- `searches.jsonl`: genuine Mathlib search records from the required `msearch.py` calls.

There are 0 new nodes and 0 Mathlib leaves. No unit record changed.

## Attachments

None. Grep searches of the read-only `WeilConjectures` trees for the item id, its blueprint tag, locally cocartesian fibrations, relative colimits, and transported fiber cocones found no sorry-free declaration stating this theorem. The ordinary relative-colimit declarations in `CategoryTheory/Pro/Basic.lean` do not match the quasicategorical statement. The upstream master source was treated as reference material only.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, Proposition 4.3.1.10 and proof (printed pp. 265–266), for the six-step local fiber criterion. I read the official PDF online at `https://www.math.ias.edu/~lurie/papers/HTT.pdf`; it is not archived under `literature/`.

WANTED: Kerodon Proposition 7.1.6.19 (tag 02X1), for the equivalent relative mapping-space/constant-target convention. I read it online; no Stacks tag states this quasicategorical assertion.

## What was wrong or incomplete

The imported node had the correct statement and source but no proof. I retained every hypothesis: an inner fibration whose edge pullbacks are cocartesian fibrations, an arbitrary small simplicial set including the empty one, a cone in one strict fiber, all outgoing edges including degenerate edges, and no global cocartesian or all-colimit assumption. The proof follows HTT 4.3.1.10 through the existing project mapping-space and transport lemmas.

No statement correction or `STATEMENT-DISPUTED` issue was needed. No new helper node was introduced: the proof's non-elementary ingredients are existing nodes, and the generic cone mapping-space criterion is declared as the sole off-unit tool use.

## Mathlib searches

I ran eight additional required searches with `msearch.py Q01 lem-coef-local-fiber-relative-colimit-test`: two LeanFinder queries, two LeanSearch queries, two Loogle queries and two Mathlib-grep queries, using two semantic phrasings. LeanFinder and LeanSearch returned ordinary `CategoryTheory.Limits`/Grothendieck colimit results; Loogle returned no usable match (one query reported an unknown identifier); grep returned no quasicategory hit and ordinary `FiberedCategory` hits. I inspected the returned signatures and source contexts. None states a relative-colimit criterion for a locally cocartesian quasicategorical fibration, so the item remains non-Mathlib.

## Not duplicates

No new nodes were created. The existing `lem-coef-infinity-fiber-relative-colimit-criterion` is the globally cocartesian special case and cannot replace the local edge-pullback hypothesis. `lem-coef-local-transport-section-colimits` assembles colimits in a section category and uses this item; citing it would be circular. `lem-coef-infinity-relative-cone-constant-test` gives only the mapping-space test and does not identify it with all outgoing transports.

## Review by Q01

I read the target node, `sec-six-functors` chapter, `sk-prop-sf-biduality-general` unit, the main-20261015 exceptional-adjoint proof paragraph 2, the stage-1 contract, and delivery-errors B–E. I opened every cited node statement and checked the proof against HTT Proposition 4.3.1.10 and its proof.

Step 1 defines the boundary, apex and coherent cocone and chooses one transport cylinder for the whole join diagram. The cocartesian mapping criterion supplies the mapping-space characterization, and the pointwise transport statement supplies the coherent diagram transport and its object/diagram homotopy-fiber formulas. The given edge-pullback hypothesis supplies the required cocartesian lifts; the strict fibers are quasicategories by inner-horn lifting over a constant base simplex.

Step 2 applies the existing constant-target relative-cone criterion to the exact cone in the item. Since the cone lies in the strict fiber, the base cocone is the identity, so the lower map is the constant-diagram map. Step 3 uses the path-pullback model, its Kan-complex path construction, and the homotopy-fiber detector over the identity of the outgoing mapping space. The explicit intermediate-path calculation identifies the relevant fiber with the fiber over the constant transformation.

Step 4 uses the same single transport cylinder in the object and diagram formulas. Its coherent naturality square identifies the actual fiber map with $v\mapsto\Delta_K(v)\alpha_f$, so no unrelated objectwise comparison is assumed. Step 5 applies the ordinary cocone mapping-space criterion in the target fiber to each specified transported cocone and proves the forward implication. Step 6 fixes an arbitrary outgoing edge and varies over every target-fiber object, giving exactly the converse cocone criterion; it explicitly retains the identity edge and the empty-shape case.

I checked the hypotheses and edge cases $K=\varnothing$, $K=\Delta^0$, identity and product fibrations, an empty base, and a non-preserving transport over $\Delta^1$. The proof never assumes weak contractibility, existence of other colimits, global cocartesian lifts, or coherence of transports under composition. Every citation quote in `citations.json` is a literal substring of the cited statement, and `proof_deps` is exactly the union of the step uses. No cycle, source error, duplicate node, or attachment was found.

## Unfinished work

No part of the one-level split remains unfinished. No Lean file, compiler, Lake, build, or live-project file was written.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q01 lem-coef-local-fiber-relative-colimit-test --no-push .` passed server preflight and both DAG/review checks: `OK (not pushed)`; the latest server receipt was `ac8917dca2`. Nothing was pushed.


## Second reading by Q01

Independent second reading, 2026-10-17. The actual group is Q01, the item is lem-coef-local-fiber-relative-colimit-test, and the stage-1 item JSON exists. The Q20/stage-2 recovery condition does not hold. This packet remains stage 1; no Lean or compiler was used. The first worker's sections above are retained; the corrections below supersede their claim that the original transport application had all its hypotheses.

- Item statement: checked clause by clause against Higher Topos Theory Proposition 4.3.1.10 and its proof, printed pp. 265–266, independently opened at https://www.math.ias.edu/~lurie/papers/HTT.pdf. The edge-pullback hypothesis is the local cocartesian condition used by the source. The arbitrary shape, empty shape, outgoing and degenerate edges, and all specified transport witnesses are retained. The join-to-coherent-cocone convention agrees with the existing relative-cone and constant-target definitions. Verdict: correct; unchanged.
- Step 1: checked the full statements of lem-coef-infinity-cocartesian-mapping-criterion and lem-coef-infinity-pointwise-cocartesian-transport, and HTT 3.1.2.1 and the edge-pullback reduction in 4.3.1.10. Verdict: repaired. The original applied the global transport theorem to the merely locally cocartesian ambient map. The repaired step applies it only to the cocartesian edge pullback, supplies existence of transport witnesses, and fixes one compatible cylinder for each specified transport. The notation p, mathcal E, mathcal B and b is now introduced explicitly.
- Step 2: checked lem-coef-infinity-relative-cone-constant-test and its underlying relative-cone definition against Kerodon Proposition 7.1.6.19 (https://kerodon.net/tag/02X1), including coherent square data and unrestricted shapes. Verdict: retained. The constant base cocone makes the bottom map exactly the constant-diagram map.
- Step 3: checked the full statements of def-coef-infinity-relative-cone, lem-coef-kan-pullback-path-comparison, and lem-coef-spaces-homotopy-fiber-detection. Verdict: retained. The path pullback is Kan; the detector is applied over the identity of S_z, a weak equivalence. Composition with the second base path gives the stated fiber over the constant transformation, including higher path data and empty mapping spaces.
- Step 4: checked the full statements of lem-coef-inner-anodyne-pushout-product, lem-coef-infinity-inner-mapping-fiber, lem-coef-kan-pullback-path-comparison, and lem-coef-infinity-pointwise-cocartesian-transport. Also checked HTT 2.3.2.4–5 and 3.1.2.1. Verdict: repaired. Inner exponentiation is obtained by the explicit lifting adjunction; the two ambient mapping-space maps are Kan fibrations. Their strict fibers are identified degreewise with mapping spaces in the chosen edge pullback, and constant paths compare them to homotopy fibers. The local transport formulas and the one cylinder's naturality square identify the actual comparison map. No local edge is asserted globally cocartesian.
- Step 5: checked the dual cocone mapping-space criterion in lem-cbc-enhanced-functor-cone-calculus against exactly the map beta supplied in step 4. Verdict: retained. Every ambient object and outgoing edge is tested, and transport witnesses exist by step 1.
- Step 6: checked the same cocone criterion with the edge and any specified transport fixed while every target-fiber object varies. Verdict: retained. This proves the universal quantifier over transports; identity and empty-shape cases are included.
- New nodes: none to remove, repair, or search individually. The repaired proof still has 0 new nodes and 0 Mathlib leaves. The two additional cited lemmas already exist in the item's unit; neither reaches the item through statement or proof dependencies. The pushout-product lemma is already a Mathlib leaf. All twelve citation records now quote the complete cited statements verbatim, so their hypotheses are visible in the packet; proof_deps is their exact union.

Changes and reasons: repaired steps 1 and 4 to remove the invalid global cocartesian hypothesis, introduced the proof's previously unbound notation, added the existing inner-mapping-fibration and inner-anodyne pushout-product dependencies, and updated the summary, provenance and citations to match. Backups of each changed existing packet file were preserved as .bak-second-reading. No target, statement, definition, unit or chapter was changed. The sole off-unit generic tool remains lem-cbc-enhanced-functor-cone-calculus, as already identified by the first worker; no maintainer tool_uses field was written.

Independent edge checks: K empty gives the initial-object criterion in every transported fiber; K a point gives that each transported cocone edge is an equivalence. For the identity fibration, all relevant mapping-space comparison maps are equivalences. For a product fibration the assertion reduces to the ordinary colimit criterion in its category factor. An empty base admits no datum s. Over Delta^1 a transition functor that does not preserve the selected colimit makes both sides fail; no preservation assumption is smuggled in. The repaired mapping-space argument works for a locally cocartesian map whose local lifts do not compose globally, since it uses one edge at a time.

Independent searches: msearch.py LeanFinder was run with the new phrasing “For an inner fibration of simplicial sets with cocartesian restrictions to intervals, a fiber cocone is relatively universal iff it remains universal under every transition functor”. Its hits concern ordinary categorical universal/Grothendieck colimits, Kan fibrations, coskeleta and strict Segal simplicial sets; none is this statement. I read the ordinary IsUniversalColimit definition in Mathlib/CategoryTheory/Limits/VanKampen.lean:44 and the Grothendieck cocone declaration in Mathlib/CategoryTheory/Limits/Shapes/Grothendieck.lean:175; their objects and hypotheses do not match. A correctly scoped msearch.py grep for IsColimit|Cocartesian|homotopyFiber under AlgebraicTopology/Quasicategory returned no hits. An earlier invocation mistakenly used --sub as a positional directory and returned no hits; its genuine log record is retained but is not evidence for absence. All searches are recorded exactly as run in searches.jsonl. No upstream source declaration matching the item was found in the independently repeated id/concept search of the permitted read-only source trees. The first worker's archive WANTED entries remain applicable.
