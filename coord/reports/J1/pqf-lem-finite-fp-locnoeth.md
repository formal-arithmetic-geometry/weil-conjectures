1. Files written:

- `dag/nodes/sec-nagata-compactification/pqf-lem-finite-fp-locnoeth.json` — statement, split proof, and Mathlib searches.
- `dag/nodes/sec-nagata-compactification/pqf-lem-lft-fp-locnoeth.json` — statement-only Mathlib leaf for the Noetherian-target conversion.
- `citations.json` — verbatim citations for every proof step.

The new node is a Mathlib match for `AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType`; there are no non-Mathlib new nodes.

2. Attachments: none.

3. WANTED: none.

4. The imported proof unnecessarily rebuilt the affine Noetherian argument and cited `pqf-lem-affine-open-locnoeth`. I replaced it with the existing stronger leaf `pqf-lem-finite-iff-integral-lft` and Mathlib's locally-Noetherian equivalence. The item statement itself was unchanged.

## Review by J1

I read the item source blueprint proof, the unit route, the locally Noetherian definition, the finite morphism conventions, the finite-type and locally-finite-presentation definitions, and the existing `pqf-lem-finite-iff-integral-lft` node. Step 1 uses exactly that existing equivalence for the locally finite type conclusion; it also checks from the finite convention that the morphism is affine, hence has the standard quasi-compact and quasi-separated properties required by the convention for finite presentation. Step 2 applies the new Mathlib leaf with the hypothesis that the target is locally Noetherian. Step 3 matches the resulting locally finite presentation property with the quasi-compact and quasi-separated properties from Step 1 using the project's finite-presentation convention. I verified every citation quote against the cited node files and tested the statement on the identity finite morphism and on a finite affine algebra over a Noetherian ring. The old affine-chart argument and its unused affine-open-Noetherian dependency were removed.

## Second reading by J1

- Item statement: checked against the blueprint node `pqf-lem-finite-fp-locnoeth` and the finite-presentation convention; hypotheses (locally Noetherian target and finite morphism) and conclusion agree.
- Step 1: checked against `lem-weil-pbc-finite-iff-integral-lft` and `def-weil-pbc-scheme-conventions`; finiteness supplies locally finite type, and the affine clause of finiteness supplies the standard quasi-compact and quasi-separated properties.
- Step 2: checked against Mathlib `AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType` (Noetherian.lean:275-276) and `pqf-def-locnoeth`; the reverse implication is the one used.
- Step 3: checked against `def-weil-pbc-scheme-conventions` and `def-sbc-locally-finite-presentation`; this is the stated conjunction defining finite presentation and is elementary from those definitions.
- New node `pqf-lem-lft-fp-locnoeth`: statement-only Mathlib leaf; checked self-contained hypotheses and definition links, exact declaration, file/line, and all three recorded searches.
- Small cases: identity of an affine Noetherian scheme, a finite field extension, and the zero finite algebra over a Noetherian ring satisfy the statement; no empty-scheme exception changes the argument.
- Changes made in this second reading: none to the worker's node or proof; appended this audit and retained the replacement of the unused affine-chart route documented above.
