# Worker report: lem-sfb-invertible-stalk-neighbourhood-section

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-invertible-stalk-neighbourhood-section.json`: statement, split; complete three-step proof, statement and statement dependencies unchanged. No exact whole-item Mathlib match.
- `citations.json`: eight step/node entries with verbatim statement quotations.
- `searches.jsonl`: the required command's own records, retained without editing.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The split uses existing Mathlib leaves, including `lem-sfb-local-ring-map-spread`; no duplication of the identical off-unit `lem-per-local-ring-map-spread`.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id and the spreading, inverse-stalk and neighbourhood-section notions found no sorry-free project declaration giving the whole item. `WeilConjectures/Mathlib/AlgebraicGeometry/Stalk.lean` contains the point/local-map helper lemmas but not the claimed neighbourhood section.

## WANTED

None: all source text used is present in the read clone.

## Errors and changes

The statement is true as written; no STATEMENT-DISPUTED or statement correction is needed. The original empty proof did not verify the over-base equation required by the spreading lemma. Step 1 now proves that equation by the bijection of 01J6 and the equality beta composed with alpha = identity, rather than assuming that any inverse stalk homomorphism has already supplied an X-morphism. Step 3 explicitly recovers both the image point and the specified stalk inverse.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor lem-sfb-invertible-stalk-neighbourhood-section` returns None. Its precise inherited `from.place` and `via` are retained. Searches of the entire imported blueprint for local ring, spreading, stalk isomorphism and 0BX6 found no equivalent blueprint item. I read the latest blueprint's unit and direct-image statement/proof (3); this local algebraic-geometric lemma realizes the inherited old step 5 of the alteration subroute, without changing the unit or its route. No unit realized fields are touched because this item is not the unit's key statement.

## Unfinished work

No mathematical part is unfinished. This is stage 1 only; no Lean source was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. The existing `lem-sfb-local-ring-map-spread` and `lem-per-local-ring-map-spread` state the same spreading result; I cite the former, in this item's unit. The item is stronger than that spreading input in a different direction: it starts with a local-ring isomorphism, constructs the required morphism over X, and extracts its point/stalk behavior. The existing 01J6 bijection and stalk-composition nodes supply those arguments.

## Review by N5

I read Stacks `varieties.tex`, Tag 0BFP, `lemma-modification-normal-iso-over-codimension-1`, proof (4), where the equality of the two local rings is spread to a section. I read `morphisms.tex`, Tag 0BX6, `lemma-morphism-defined-local-ring`, statement and proof (2)(c); its base-relative hypothesis is essential, and it allows a locally finite-type target and locally Noetherian source without separatedness or properness. I also read `schemes.tex`, Tag 01J6, `lemma-morphism-from-spec-local-ring`, and Equation 02NA, `equation-canonical-morphism`, and `sheaves.tex`, Tag 008M, `lemma-compose-f-maps-stalks`. There are no new nodes requiring further sources.

For step 1 I opened the statements of `lem-weil-pbc-morphism-from-spec-local-ring`, `lem-weil-pbc-spec-local-ring-canonical-morphism` and `lem-weil-pbc-scheme-stalk-map-composition`. The first gives precisely the morphism/pair bijection with normalized closed-point stalk map. The second says that the canonical morphism corresponds to (x,id). The third explicitly gives the composition formula, not merely a definition of stalks. Their statements justify constructing phi from (y,beta), computing the pair of f composed with phi as (x,beta composed with alpha), and proving equality to c_x by injectivity. I checked the variance: alpha goes from O_X,x to O_Y,y and beta goes back, so this composition is the identity on R. A ring isomorphism has local inverse because it preserves units and nonunits.

For step 2 I read the whole statement of `lem-sfb-local-ring-map-spread` and Mathlib `AlgebraicGeometry/SpreadingOut.lean:374-386`. It gives both equalities used here: h composed with c_t,W = phi and g composed with h = a restricted to W. Set S=T=X and a=id, g=f; the over-base equation is exactly the one proved in step 1. The assumptions locally Noetherian X and locally finite-type f match verbatim. Mathlib's locally Noetherian germ-injectivity instance is at lines 170-191; no extra integral or separated hypothesis is being smuggled in. The search hits were read, including the unprimed form at line 335 and `SpecToEquivOfLocalRing` at `Stalk.lean:395`. They provide the existing ingredients; neither alone states every clause of this item under its initial data. Both semantic phrasings, Loogle, LeanSearch and the grep were run through msearch and recorded exactly, retaining the inherited searches as history.

For step 3 I again checked the canonical-morphism, bijection and composition statements: applied to W, the canonical map at its closed point has the identity normalized stalk under O_W,x=R, so composing it with s recovers beta, and its point is x. The only remaining argument is the universal property from `def-pc-fibre-product`: the pair (s,id_W) defines the factorization into Y times_X W, and the second projection is the identity. This is why that step is elementary relative to the cited statements, not a hidden new geometric theorem. The off-unit canonical-morphism result is declared in `split_report.tool_uses` as a generic tool; the other off-unit statements are Mathlib leaves.

Against B-E, I checked all eight step citations against their statements and generated their verbatim quotes in citations.json. No statement-only node carries a concealed proof, no new definition or unsearched node was introduced, and no clause was moved into a renamed lemma. The proof dependencies are exactly the union of the uses. Every step is shorter than 2000 characters and the entire assembly is shorter than 3000. The operations only use schemes, local maps, opens and the stated fiber-product universal property. Edge cases: if Y is empty there is no y; X empty is then impossible; arbitrary nonclosed x and nilpotent/nonreduced locally Noetherian X remain allowed, since 0BX6(2)(c) uses neither reducedness nor closedness. The identity morphism gives beta=id and an ordinary identity section. A disjoint union over X may admit extra branches, but the statement asks only for a section through the chosen y, so no unwarranted local isomorphism of f is claimed. No SGA source is used, and no dependency points back to this item.
