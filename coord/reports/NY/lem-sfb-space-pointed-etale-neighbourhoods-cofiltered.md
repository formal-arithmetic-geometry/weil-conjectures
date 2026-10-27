# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-pointed-etale-neighbourhoods-cofiltered.json`: statement, split; no exact Mathlib match. Five complete steps, all original metadata and statement retained.
- `citations.json`: one checked verbatim quotation for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the prescribed search tool's log; `write_split.py` is an item-local construction script, not a delivery node.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the live read-clone `lean/WeilConjectures/` by the exact blueprint tag and id and by algebraic-space, pointed-etale-neighbourhood and cofiltered terminology. The scheme neighbourhood declarations and their occurrences do not state the algebraic-space assertion. No complete project declaration was found.

## Literature wanted

None.

## Findings and changes

The item had an empty proof. Its statement is faithful to spaces-properties.tex Tag 04JW (lemma-cofinal-etale), restricted to scheme objects as explained before the lemma and after Tag 04JY (definition-stalk). No statement correction is necessary. Nonemptiness is supplied explicitly, rather than pretending that the algebraic space X itself is a scheme object of its small site.

I read the unit and chapter records, the latest blueprint direct-images proof (3), and the inherited auxiliary provenance. This is an existing geometric-stalk prerequisite of that branch, not a replacement of the unit's route. The existing `blueprint.from.node = null` and long `via` list were retained as the ancestor command reported; `from.place` already specifies the 04JW/04JY prerequisite. Blueprint searches for cofiltered, etale neighbourhood, and cofinal-etale found no duplicate algebraic-space assertion. In particular the scheme-base neighbourhood result is not a duplicate: its final object is the scheme base, unavailable here. The proof writes the common-refinement and diagonal arguments rather than moving the conclusion into new nodes.

The prescribed five Mathlib searches were run and their hits read; the existing item already records these exact queries and their actual results, so those records were retained. I inspected Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean, especially lines 34–57 and the point construction following them, and Sites/Point/Basic.lean. The EtalePoint cofiltered instance at line 56 assumes a scheme S. Point.isCofiltered is a generic consequence for an already constructed site point, and does not construct the algebraic-space point required here. Thus neither is a one-line specialization for this item. The alternative semantic search likewise returned schemes, site definitions and inverse-system lemmas, not this assertion.

## Unfinished work

None in this one-level split. The mathematical proof is complete relative to existing cited nodes; no new node awaits a split. No Lean was written and no compiler, Lake or build tool was run. All authored files are in the assigned sandbox.

## Not duplicates

No new nodes were created. Existing generic tools were reused, including `lem-trf-space-representable-etale-scheme-tests` instead of creating a second algebraic-space fibre-product/permanence package.

## Review by NY

I read spaces-properties.tex Tag 04JW with its whole proof and the paragraph following 04JY, and morphisms.tex Tag 02GL (lemma-etale-over-field), both clauses. I compared the item with these passages and with the latest blueprint ambient direct-images proof (3). I also opened and read the statements of every cited DAG node, including the full representable-etale scheme-test package. The following is my check of each actual inference, not a claim that a script reviewed the mathematics.

Step 1 uses the size convention's explicit instruction to work with a small skeleton. The lifts over each site object are a subset of a scheme hom set, so a set-indexed union is small in the containing universe. The representative replacement is written with an isomorphism and inverse, so the constructed pointed maps remain maps of the chosen site; there is no assumption that the chosen skeleton is literally closed under fibre products.

Step 2 uses the atlas and scheme-test surjectivity/etaleness in def-trf-algebraic-space, not a theorem supposedly hidden in that definition. The scheme base change E exists and is surjective and etale by exactly those clauses. The fibre node explicitly states decomposition into finite separable field spectra for every etale scheme morphism, so it applies to E over Spec Omega with no finite-type, quasi-compactness or separation assumption. Its fibre is E since the base is the spectrum of a field. Nonemptiness chooses a component. The fact that its field equals Omega is proved inline by factoring an annihilating polynomial into linear factors, using the stated root definition of algebraic closedness. This proves an actual scheme section over the *same* Omega, not merely a lift after a field extension. The atlas then supplies a scheme neighbourhood of the required point.

Step 3 cites lem-trf-space-representable-etale-scheme-tests for precisely its stated scheme representability, base change, and composition clauses. Both input maps have scheme sources and are etale over X, so their product is a scheme, not merely an algebraic space. Its marked point exists by equality of the two maps to X. The explicit pair gives both required pointed arrows. No theorem about products merely at the level of underlying point sets is substituted for the sheaf fibre product.

Step 4 uses the final clause of the same scheme-test lemma: V and P are schemes, both structure maps to X are representable etale, and the pair map is over X. Hence r is etale. The scheme fibre-product node explicitly gives existence and the universal property for W over the *scheme* P. Base change of r along the scheme map Delta gives W to U etale; composing gives W to X representable etale. Both q and p are specified, and the equation from the pullback square shows h1 p = q = h2 p. The marked point is supplied by the actual equality r bar-v = Delta bar-u. Thus the conclusion is equality of morphisms, not equality on geometric points. This follows the exact Stacks square and does not need the separate open-diagonal theorem (which in the existing DAG only has scheme target).

Step 5 only reverses the three established axioms and uses the filtered-category meaning explicitly written in def-weil-pbc-category-colimit. Its elementary designation is limited to this unpacking and Step 1's set/skeleton argument; none of the geometric existence assertions is marked elementary. Every step is shorter than 2000 characters.

I checked edge cases: X empty cannot admit the stipulated geometric point, so no empty atlas fibre is chosen; input neighbourhoods with a lift are nonempty; if the two arrows agree, the same square still produces a valid pointed equalizer. Infinite, non-quasi-compact atlases and nonseparated etale morphisms cause no change, since none of the cited statements requires finiteness or separatedness. The field Omega is used as algebraically closed only for the atlas lift. The sources impose no assumptions on S omitted by this item.

Against delivery-errors B–E: there are no new nodes to hide a proof in, duplicate, leave ill-typed or falsely label as a Mathlib leaf. All statement notions remain defined inline or by the original statement dependencies. Every non-elementary input is a cited existing statement, and citations.json quotes those statements verbatim. Off-unit generic tools are declared in split_report.tool_uses with their precise roles, without setting the maintainer-owned tool_uses field. The statements do not depend on the item and the server DAG check will verify absence of cycles. No source error or weakening was found. The report preserves the null blueprint ancestor reported by the official ancestor command rather than inventing an ancestor.
