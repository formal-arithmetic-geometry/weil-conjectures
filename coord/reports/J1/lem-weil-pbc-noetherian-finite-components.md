1. Files written:

   - `dag/nodes/sec-smooth-purity/lem-weil-pbc-noetherian-finite-components.json`: statement, Mathlib leaf.
   - No new nodes.

2. Attachments:

   - Existing DAG node `lem-weil-pbc-noetherian-finitely-many-components` in `sec-proper-base-change` states the same scheme-level result and is already a Mathlib leaf; this delivery keeps the present blueprint item as its own node.

3. WANTED: none.

4. The imported blueprint says the assertion is already in Mathlib. I found no project declaration with this item's blueprint tag in either source checkout. The Mathlib theorem is exact, so no proof split or additional dependency node is needed. The source path named by the imported node is not present in this checkout, but the embedded blueprint proof text and the Mathlib source establish the intended statement.

5. What I could not finish: none.

## Review by J1

I checked the item node and its embedded blueprint text, then read Mathlib's `Mathlib/AlgebraicGeometry/Noetherian.lean` lines 358–365. The theorem `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian` has hypothesis `[IsNoetherian X]` and conclusion `(irreducibleComponents X).Finite`, exactly the scheme statement. Its proof invokes the general `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` theorem after Mathlib supplies the Noetherian-space instance; no unstated hypothesis is used. I searched the DAG and blueprint for duplicate statements and found the existing proper-base-change node and the more general topological-space leaf; neither requires a new node here. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the LeanSearch service was unavailable, and the grep service returned no hit for its requested subdirectory, so those results are recorded verbatim with their actual verdicts. The direct Mathlib source check supplied the exact declaration and line recorded in `mathlib_match`. No proof steps or citation quotes are needed for a Mathlib leaf, so `citations.json` is empty.

## Second reading by J1

- Item statement: checked against Stacks Properties Lemma 0BA8, label `properties-lemma-Noetherian-irreducible-components`, which states that a Noetherian scheme has a finite number of irreducible components; verdict exact.
- New nodes: none; the existing item node is converted to a Mathlib leaf, so no new statement requires B1–B7 review.
- Proof steps: none; the Mathlib declaration `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian` is an exact leaf, with the inferred `IsNoetherian` hypothesis and finite irreducible-component conclusion checked at `Mathlib/AlgebraicGeometry/Noetherian.lean:364`.
- Small cases: the empty scheme, a field spectrum, and a scheme with one or finitely many components all satisfy the statement; no extra hypothesis is present.
- Existing duplicate: `lem-weil-pbc-noetherian-finitely-many-components` states the same general fact, but it is a separate already-landed tool node; this delivery changes only the required blueprint item and adds no duplicate node.
- Changes: corrected the source from the unavailable blueprint path to Stacks tag 0BA8 and recorded the second-reading audit; Mathlib search records and the empty citations file remain unchanged and truthful.
