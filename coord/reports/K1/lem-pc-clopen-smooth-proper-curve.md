# Stage 1 report: lem-pc-clopen-smooth-proper-curve

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-clopen-smooth-proper-curve.json`: item, split.
- `dag/nodes/sec-picard-framework/lem-pc-open-immersion-smooth-composition.json`: statement, Mathlib leaf.
- `citations.json`: verbatim citations for both proof steps.

## Attachments

None. A search of the slopmaster2 `WeilConjectures` and `Comparator` trees found no declaration tagged `lem-pc-clopen-smooth-proper-curve` or stating this result without `sorry`.

## WANTED

None. The Stacks source is already identified by Tags 01VC, 01VA, 01W5 and 01W3 in the item and the existing properness leaf.

## Review by K1

I read the item node, its unit `sk-thm-picard-rr`, the parent blueprint route through `lem-pc-ample-positive-degree`, and the Stacks Morphisms tags recorded in the source fields. The item statement now introduces the field, the smooth proper structure morphism, and a nonempty scheme with a morphism to the ambient scheme that is explicitly both open and closed; its hypotheses therefore match the two permanence arguments. I searched the whole DAG and blueprint for an existing open-immersion-smooth statement and found no suitable node. The existing `lem-weil-pbc-closed-immersion-proper` node was read in full; its clause (b) says exactly that a closed immersion followed by a proper morphism is proper, which is the fact used in step 2.

Step 1 cites `lem-pc-open-immersion-smooth-composition`, whose statement explicitly takes an open immersion and a smooth morphism and concludes that their composite is smooth. The step instantiates it with `i : Z -> Y` and the structure morphism of `Y`; no dimension or nonemptiness hypothesis is smuggled in. Step 2 cites the existing properness node and uses only its verbatim clause (b), with the closed immersion `i` and the proper structure morphism of `Y`. Both steps are marked non-elementary because they invoke permanence theorems rather than one-line definition unfolding. The `citations.json` quotes are copied verbatim from the cited node statements.

For the new leaf I read Mathlib `AlgebraicGeometry/Morphisms/Smooth.lean`: the open-immersion `Smooth` instance is at lines 181--184 and the relative-dimension composition instance at lines 207--214, which specialize directly to the new statement. I recorded LeanSearch, Loogle, and source grep searches, and found no duplicate DAG or blueprint node. I tested the statement on the identity open immersion (giving the original smooth morphism) and on an open component of a disjoint union; both satisfy the conclusion. For the item, the empty-scheme edge case is excluded by the explicit nonemptiness hypothesis, while a full clopen component (`Z = Y`) reduces to the given smooth proper morphism. No source or statement error was found.

## What was wrong or corrected

The imported item said “open-and-closed subscheme” without explicitly introducing the two morphism properties needed by the proof, and it had no proof split. I replaced that shorthand with explicit open and closed immersion hypotheses, added the corresponding statement dependencies, and supplied the two permanence steps. The source’s existing properness node was reused rather than duplicated.

## Unfinished

Nothing.
