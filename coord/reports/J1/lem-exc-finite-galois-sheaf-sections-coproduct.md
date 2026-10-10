# Stage-1 report

## Files written

- `dag/nodes/sec-curve-estimates/lem-exc-finite-galois-sheaf-sections-coproduct.json`: statement node, split; no Mathlib leaf.
- `citations.json`: verbatim citations for both proof steps.

## Attachments

None. No sorry-free project declaration with the exact item statement or blueprint tag was found in `WeilConjectures/` of either source checkout.

## WANTED

None.

## What was checked and changed

The original node had the correct statement but no proof. I kept its hypotheses and dependencies, filled the blueprint proof location, and added two steps following Stacks Tag 03SF. Step 1 uses the existing coproduct-family statement to obtain open, pairwise disjoint, jointly covering coprojections; open immersions are etale by the site conventions. Step 2 applies the existing set-valued etale sheaf equalizer definition. Empty overlaps make the compatibility condition vacuous, and the empty-cover instance gives that the value on the empty object is a singleton, so restriction is the claimed product bijection with unique gluing. The finite empty-family case was checked explicitly.

## Review by J1

I read the item's source reference, Tag 03SF in `literature/stacks-project/pione.tex`, and checked the neighboring imported proof in `lem-exc-finite-galois-sections-descent.json`. I opened `lem-weil-pbc-scheme-coproduct-family.json`: its statement explicitly gives the coproduct universal property, open coprojections, pairwise disjoint images, and their union, exactly what Step 1 takes. I opened `def-weil-pbc-etale-sheaf-of-sets.json`: its statement explicitly gives the equalizer diagram for every etale covering and the two restriction maps, exactly what Step 2 takes. The etale nature of an open immersion and the singleton value on the empty object are immediate from the cited site/sheaf definitions and were kept as elementary consequences rather than new nodes.

I searched the whole DAG and blueprint for a set-valued sheaf-on-coproduct statement. The existing abelian-sheaf clopen-product node is a different statement and was not duplicated. I searched the source for the item id, its blueprint tag, and the relevant finite-Galois/sheaf-section terminology; no exact project declaration exists. I ran the required LeanFinder, Loogle, grep, and LeanSearch queries in two phrasings. LeanFinder returned only topological-sheaf/general equalizer infrastructure; Loogle and grep returned no matching etale-scheme theorem; LeanSearch was unavailable both times, recorded as unavailable. Small cases checked were one summand (identity restriction), the empty family (singleton product and empty-cover sheaf value), and two disjoint summands (ordinary pairwise gluing).

No source error or unfinished proof remains in this split.

## Second reading by J1

- Item statement: checked against the finite disjoint-union section calculation cited at Stacks Tag 03SF, with the small-etale-site definitions; hypotheses for the scheme, sheaf, finite coproduct, disjoint overlaps, and empty value are all explicit and the restriction/product conclusion is correct.
- Step 1: checked against `lem-weil-pbc-scheme-coproduct-family` and `def-weil-pbc-etale-sheaf-of-sets`; the former supplies open, disjoint, covering coprojections and the latter supplies the etale covering convention. The implication that open immersions are etale and the empty overlap computation are elementary.
- Step 2: checked against the full equalizer clause of `def-weil-pbc-etale-sheaf-of-sets`; with singleton empty sections, all compatibility maps from empty overlaps are equal, so the equalizer is the product, including the empty finite family.
- New nodes: none; the item is the only split node, so B1-B7 and duplicate searches were checked on the item itself and no auxiliary node was created.
- Edge cases: one summand gives the identity restriction, two summands give ordinary disjoint gluing, and the empty family gives the singleton-to-singleton bijection.

Changes made: corrected the node's `created.item` to this delivery item (it incorrectly named the tensor-decomposition item), and replaced abbreviated citation snippets with verbatim portions of the cited definition's equalizer statement. No mathematical statement or proof step required alteration.
