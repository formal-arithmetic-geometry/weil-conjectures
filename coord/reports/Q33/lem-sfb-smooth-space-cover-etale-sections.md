# Q33 stage-1 report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-space-cover-etale-sections.json` (statement, split; not a Mathlib match), `citations.json`, and this report. No new nodes; no Mathlib leaves. `searches.jsonl` records four searches made by the required launcher command.
2. Attachments: none. A search of `lean/WeilConjectures/` for the exact blueprint tag found no declaration; searches for algebraic spaces and smooth/etale local sections found no declaration stating the item. In particular scheme-only and sheaf-section results cannot attach the algebraic-space assertion.
3. WANTED: none.
4. The imported item had no proof. Its statement and statement dependencies are preserved. The source atlas reduction is sound; instead of creating the scheme-only local-section consequence of 055U/055V, this split cites the already existing and stronger smooth slicing theorem `sbc-lem-slicing`. This is a generic tool below the unit route. Its sections give actual maps into the original space, and the proof verifies that the resulting etale base maps cover the target.
5. Unfinished mathematics: none for this one-level split. The supporting nodes retain their own stage states. No Lean files or compiler/build tools were used.

## Sources and searches

Read the current blueprint in `literature/blueprint/latest/`: the unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, its `sk-thm-sf-ctf-stability-direct-images.proof.md`, and `sec-smooth-base-change/sk-prop-normal-form/sbc-lem-slicing.md` with its proof. Also read the chapter and unit DAG records. The geometric local-section lemma is a supporting input far below the direct-image alteration route, so the proof does not replace any unit step.

Read Stacks `spaces-topologies.tex`, Tag 0CFV, label `lemma-etale-dominates-smooth`, in full. Its first reduction replaces each smooth source by an etale scheme atlas. Read `more-morphisms.tex`, Tags 055U (`lemma-etale-nbhd-dominates-smooth`), 055V (`lemma-etale-dominates-smooth`), and 0EY4 (`lemma-cover-smooth-by-special`). The last statement already occurs as the blueprint/DAG node `sbc-lem-slicing` and is enough to implement the scheme refinement without another node. Read the existing algebraic-space definition and atlas theorem, including their proof descriptions. Point-surjectivity is taken from the explicit atlas theorem rather than silently equating representable surjectivity with a different point convention.

The whole-DAG scan compared statements and source tags 055U, 055V and 0CFV, and smooth local-section/refinement statements. `lem-sfb-projective-frames-pgl` only includes smooth torsor local triviality, so it neither supplies this general algebraic-space theorem nor needs a duplicate here. The blueprint searches `smooth.*section`, `055U`, `055V`, `local sections`, `slicing`, and `etale covering` found the existing slicing theorem and no exact duplicate of the item. No new node is created.

Mathlib searches, all run by `msearch.py` and read: LeanFinder for smooth surjective algebraic spaces admitting sections over an etale cover, Loogle for `"Smooth", "section"`, grep for `AlgebraicSpace|smooth.*etale.*section|smooth.*surjective.*section`, and LeanSearch for refinement of smooth algebraic-space coverings by etale scheme coverings. The grep returned no hits; Loogle found the smooth manifold sheaf section theorem. Semantic hits are scheme smoothness/standard-smooth presentations, affine-space surjectivity, and etale site definitions. Read Mathlib's `AlgebraicGeometry/Morphisms/Smooth.lean` and `Etale.lean` near the local-chart and composition declarations; they do not state the algebraic-space result. The two semantic searches use different phrasings. New results were appended to the item's existing search records, which were retained.

## Review by Q33

I checked delivery-errors B through E, including both copies in the merged file, against the actual statements and sources. There are no new statement-only nodes to audit and no new notions to define. The unchanged item introduces its base scheme, target scheme, source space, smoothness convention, point-surjectivity convention and bounded universes. Its five existing statement dependencies define the notions it names; the proof needs no extra finiteness, separation, dimension, coefficient or characteristic assumption.

Step 1 is the empty-set argument. There is no assertion of a section over an empty-source map onto a nonempty target.

Step 2 uses `lem-a1-space-affine-etale-cover`: its statement explicitly gives a representable surjective etale scheme atlas AND surjectivity on field-valued point classes. I read that statement, not merely its proof. Applied to the given V over S it meets every hypothesis, including the universe convention. The composite q is smooth by precisely the item's definition of smoothness on etale scheme charts. Surjectivity of q is the elementary composition of the two surjective maps of point classes; this does not require a lift over the identical residue field. Thus q has exactly the scheme smoothness hypothesis needed next.

Step 3 uses `sbc-lem-slicing`. Its statement applies to an arbitrary smooth morphism of schemes, with no Noetherian, proper, separated, finite-type-global, or field assumption. It gives an etale cover of W, etale maps T_i to T, a factorization, and a section of each U_i to T_i. These are exactly the data the step uses; connectedness of the fibres is not needed. I checked the Stacks 0EY4 statement and current blueprint statement against this node.

Step 4 uses only the previous data and `def-weil-size-convention`. The equation p a b_i s_i = e_i r_i s_i = e_i proves the required lifting, with the section on the correct factor r_i. For coverage, the point u above w maps to r_i(u) above t, so no unjustified assertion that a section has the same chosen point as u is made. The index set is that of the existing etale cover, taken within the fixed bounded universes and skeleton; there is no colimit over a large category and no new coproduct construction. The cited size statement explicitly prescribes these universes and small skeletons. `citations.json` copies the full statement of each node cited in each step verbatim.

Small cases checked: empty T uses the empty cover; identity V=T gives trivial local lifts; a smooth projection has the expected sections; a nontrivial finite separable field extension need not have a section over the original field, but an etale cover is permitted and the argument does not assert a global section. Non-quasi-compact and nonseparated targets are allowed: neither supporting theorem imposes those restrictions, and the proof uses a set-indexed cover, not a finite subcover. An empty V over nonempty T is excluded by surjectivity. No non-elementary fact is hidden in an elementary step: after the two theorem applications, composition of maps, the identity for a section, and the cover-of-a-cover point chase are the only operations left. All steps have fewer than 2000 characters.

The two off-unit citations are declared in `split_report.tool_uses`: the atlas theorem and scheme slicing are generic geometric tools, supplying the source's scheme reduction and refinement. No circular dependency is introduced by a new node, since there are no new nodes.

## Blueprint provenance issue

`tools/blueprint_refs.py ancestor lem-sfb-smooth-space-cover-etale-sections` prints `None`. Following the live created.item chain shows it ends at `Sheaf.SixFunctors.CtfStabilityDirectImages`, which is a Lean module name rather than a DAG id. The item's inherited `blueprint.from.node` is already null, while its filled place explicitly names `det-thm-sf-ctf-stability-direct-images`, proof (3), and the full intervening geometric route. I preserved this inherited metadata and explained the intended support in split_report.blueprint; I did not edit another node or invent an ancestor different from the command's result. There are no new nodes requiring a computed ancestor.

## Not duplicates

No new nodes. The stronger existing nodes `sbc-lem-slicing` and `lem-a1-space-affine-etale-cover` are reused directly.
