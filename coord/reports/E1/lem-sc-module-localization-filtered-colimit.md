Files written:

- `dag/nodes/sec-picard-framework/lem-sc-module-localization-filtered-colimit.json`: statement node, split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citations for the proof steps.

Attachments: none.

WANTED: none.

What was wrong or incomplete: the imported node was unsplit and its `created.item` pointed to the upstream Koszul item. I corrected the ownership to this item, added the missing colimit statement dependency, and supplied the proof and split metadata. No new node was needed: the existing localization definition and filtered-colimit element/equality theorem state the required inputs. The source is Stacks Algebra Tag 00CM; its label is recorded in the node. The required Mathlib searches were run with `msearch.py`; LeanSearch was unavailable, while LeanFinder, Loogle, and grep returned no exact theorem.

What I could not finish: nothing.

## Review by E1

I read the item statement, its source reference (Stacks Algebra Tag 00CM), the ancestor blueprint clause, and the statements of `def-weil-pbc-module-localization`, `def-weil-pbc-category-colimit`, and `lem-weil-pbc-filtered-colimit-modules-elementwise`. Step 1 uses the category-colimit definition for the natural-number filtered index and the localization definition for the fraction maps; the compatibility calculation is elementary. Step 2 uses the localization statement that every element is a fraction and the existing colimit representative statement to identify a stage representative. Step 3 uses the localization equivalence relation to obtain a power `f^r` annihilating the cross-multiplied difference, then uses the existing filtered-colimit equality criterion after transporting to stage `E=e+d+r`; the displayed exponent calculation was checked directly. Step 4 is the elementary conclusion that a linear bijection is an isomorphism.

I checked edge cases `M=0`, `f=0` (both constructions collapse exactly when the relevant power kills the numerator), `f=1` (the diagram is constant with identity transitions), and a field with nonzero `f` (the map is the evident identification with `M`). I also checked that every cited quote in `citations.json` is copied verbatim from the cited node statement, that all proof dependencies are the union of step uses, and that no duplicate child node was introduced.

## Second reading by E1

- Item statement: checked against Stacks Algebra Tag 00CM and the existing one-element localization definition; the powers-of-`f` localization and fraction formula use the correct definition node.
- Step 1: checked filteredness against `def-weil-pbc-category-colimit`, and fraction maps and compatibility against `def-weil-pbc-module-localization-away`; the calculation is elementary.
- Step 2: checked fraction representatives against `def-weil-pbc-module-localization-away` and stage representatives against `lem-weil-pbc-filtered-colimit-modules-elementwise`; surjectivity follows.
- Step 3: checked the localization equality criterion and common-stage equality criterion; with `E=e+d+r`, the transported difference is exactly `f^r(f^d m-f^e n)`.
- Step 4: checked that a linear bijection is an isomorphism; elementary.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous. Existing localization and filtered-colimit nodes were read and used instead.
- Edge cases checked: `M=0`, `f=0`, `f=1`, a field with nonzero `f`, and stages `e=0` or `d=0`; all formulas remain valid.

Changes made: replaced the generic localization dependency with the existing `def-weil-pbc-module-localization-away`, which explicitly defines `M_f`, powers of `f`, fraction equality, and the localization map; updated proof uses and citations accordingly.
