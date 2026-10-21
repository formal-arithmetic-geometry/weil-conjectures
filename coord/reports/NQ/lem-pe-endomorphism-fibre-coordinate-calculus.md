# Stage-1 report: lem-pe-endomorphism-fibre-coordinate-calculus

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-endomorphism-fibre-coordinate-calculus.json`: statement item, now split into six elementary component calculations. Statement, statement dependencies, provenance and inherited searches retained. Seven actual searches from this attempt appended. Mathlib verdict: no exact match or one-line specialization for the full contract.
- `citations.json`: nine entries, one verbatim statement quotation for every step/node citation.
- `report.md`: this report. No new nodes, Mathlib leaves, unit edits, or Lean files.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item tag, endomorphism/fibre/fiber terminology and mappingCocone. `CategoryTheory/Triangulated/DerivedLimitTowerRoosTriangle.lean` proves a tower-derived-limit result, not this general endomorphism-pair coordinate contract. The additional `lean/Sheaf/Algebra/Homology/RoosConeCalculus.lean` has `sorry` in its theorem at line 282 and concerns strict inverse towers of module sheaves. Its signed-shift companion handles only the shift clause. Neither supplies an attachment for every clause of this item.

## WANTED

None. All sources needed for this elementary calculation are present.

## Problems found and changes

The existing item had a complete and correct statement but no proof. I retained it exactly and supplied the argument. There was no prior sandbox split or report to recover. The pair-category morphisms require strict intertwining, and the strict augmentation requires exactly `sJ=0`; neither may be replaced by a homotopy-commutativity assumption in these formulas. I explicitly kept these hypotheses.

The source is the current blueprint `main-20261015`, `sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`, Cones paragraph. Its parent proof says “Both constructions are functorial on complexes” and “Shifts are clear”. This item supplies those elementary details for the endomorphism fibre and strict augmentations; it does not replace the unit's derived-Nakayama route. I read the chapter and `dag/units/sk-lem-pe-derived-nakayama.json`; this item is not the unit's key statement, so there are no realized-field edits. The proof is marked agent-written, since the detailed calculations are mine and the blueprint is agent-written.

For the coordinate convention I read `literature/stacks-project/derived.tex`, Tag 014E, `definition-cone`, and `homology.tex`, Tag 011G, `definition-shift-cochain`. I checked the tag-to-label mappings in `tags/tags`. These give the cone matrix and the differential `(-1)^r d` for every integer shift, with no bounds. Reordering the [-1]-shifted cone gives precisely the item's negative sign in `-du-sv`. No source correction or STATEMENT-DISPUTED is needed.

## Mathlib and duplicate searches

Searched the whole DAG for 014E, 011G, definition-cone, definition-shift-cochain, coherent shifts, and endomorphism fibres; searched the project Lean source by tag and concept. Ran `tools/blueprint_refs.py ancestor` for the item and blueprint searches for `mapping fibre`, `shift`, `endomorphism`, `signed fibre`, `fibre`, and `mapping cocone`. The nearest blueprint ancestor is `det-pe-derived-nakayama-first-reduction` via `lem-pe-roos-cone-calculus` as recorded; no blueprint node states the entire item. The existing `def-sp-abelian` and `def-weil-abstract-derived-category` give all the structural input needed.

Read the statements of `lem-weil-signed-mapping-cocone-shift`, `lem-amb-signed-fibre-shift`, `lem-amb-signed-fibre-complex`, and `lem-pe-endomorphism-fibre-double-cone`. The first is a general signed-shift result, the next two concern fixed functors into Ab (one uses the positive cross-term convention), and the last is the double-cone comparison. None states the present full additive-functor/shift/strict-augmentation contract. I did not create any duplicate of their statements: the shifts here are verified in a few component equations rather than creating a node for a clause of the item.

All seven searches of this attempt ran through the required `msearch.py NQ lem-pe-endomorphism-fibre-coordinate-calculus` command; the unmodified records are in `searches.jsonl`, and the queries were copied exactly into the item's `mathlib_searches`. All services answered successfully. Two different LeanFinder phrasings were used. Read the returned names and then their likely relevant sources: Mathlib `Algebra/Homology/HomotopyCategory/MappingCocone.lean` lines 29–60, 209–309; `Shift.lean` lines 135–150, 240–265; `SpectralObject.lean` lines 27–43; `MappingCone.lean` lines 630–650; `Pretriangulated.lean` lines 410–435. `mappingCocone` defines the shifted cone; `lift` constructs individual maps; `composableArrowsFunctor` is the cone functor; `commShiftMapCochainComplex` concerns functors induced by coefficient functors. None is a one-line specialization stating the whole item with its specified comparisons and augmentation identities. The inherited search records are retained rather than relabelled as this worker's calls.

## Not duplicates

No new nodes are proposed, so there are no new/existing same-tag pairs to resolve. The related statements and their different scope are described above.

## Review by NQ

I reread the item, its source Cones paragraph, the two cited node statements and the Stacks cone/shift definitions with the proof steps open. Every step is a direct calculation in finite biproducts, not an invocation of an unstated cone theorem. I checked delivery-errors B–E, including both copies in the merged file.

Step 1 uses `def-sp-abelian` exactly for preadditivity, finite biproducts and bilinear composition, and `def-weil-abstract-derived-category` exactly for complexes and their morphisms. The displayed intertwining equations verify composition and sums, so the category and additive structure are constructed, not assumed. Step 2 uses the actual cone matrix stated in `def-weil-abstract-derived-category`; negating the differential for [-1] and swapping summands gives the claimed signs. The calculation of D squared uses only the hypothesis that s commutes with d. I checked that the biproduct coordinates can be read as maps from any test object, so there is no assumption that an arbitrary abelian category has underlying elements.

Step 3 uses the chain-map definition in `def-weil-abstract-derived-category` and the bilinearity supplied by `def-sp-abelian`; it writes both composites and uses exactly a d = d a and a s = t a. Its identity, composition, zero and addition equations verify the full additive functor. Step 4 uses the shift convention in `def-weil-abstract-derived-category`; iteration (or inverse iteration for negative r) gives the integer sign convention of Stacks 011G. I recomputed both source and target differentials and both sides of the chain-map equation; the sign squares to one, giving the inverse without any extra assertion. Step 5 uses only shifted maps as reindexed chain maps from the same definition. Both sides of naturality are written, and the successive-shift order is explicitly from K(V[r][r']) through K(V[r])[r'] to K(V)[r][r']. Multiplication of the two signs proves the addition law, including mixed positive and negative shifts.

Step 6 again uses the chain-map and shift definitions and biproduct projections. The assumption sJ=0 kills exactly the second differential component. The equality aJ=J'g gives both augmentation composites component by component; tJ'=0 verifies the target augmentation is a chain map. Shifting preserves sJ=0 and leaves the second augmentation component zero, so the very same sigma is used in the last identity. No exact products, derived limits, homotopy lifting, boundedness, or exactness theorem is smuggled into any step. `citations.json` has a verbatim quotation from each cited node's statement for every use, checked as a literal substring.

Small cases checked by substituting into the displayed matrices: V=0; the zero endomorphism (direct sum with the negative differential on the second summand); the identity endomorphism (cross-term -v); r=0,1,-1,2; successive shifts 1 and -1; zero J and identity J when s=0; and a nonzero differential with a commuting endomorphism. For the latter, on the two-term complex Z --2--> Z and s=3, the cross-term in D squared is 2*3-3*2=0. Thus the checks detect both a wrong cross-term sign and an omitted differential sign. All calculations are characteristic-independent, including when minus equals plus. There are six steps, each well below 2000 characters; no long step hides a separate lemma. No new node is an elementary fact or a restated clause, because there are no new nodes.

## Unfinished work

None in the mathematical split. The required server dry run and push are recorded below after they finish.
