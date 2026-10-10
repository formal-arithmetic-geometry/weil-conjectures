# def-sc-rational-functions

## Files written

- `dag/nodes/sec-abelian-varieties/def-sc-rational-functions.json`: definition marked `split`; statement and existing dependency `[def-pc-scheme]` unchanged; no new nodes or Mathlib leaves.

## Attachments

None. The source search found no sorry-free declaration stating this definition exactly.

## WANTED

None. The Stacks source is available in the local literature checkout.

## What was wrong in the node, blueprint, or brief

Nothing required correction. The imported node already gave the section-valued formulation, the correct Stacks tags and labels, the Mathlib searches, and the parent blueprint reference. A full DAG search found no existing basic dense-open or rational-function definition node to cite. The word “dense” is used as an elementary topological predicate throughout the existing DAG, while the scheme/open-subscheme notions are supplied by `[def-pc-scheme]`; creating a duplicate foundational node would not improve the split.

## What I could not finish

Nothing. This was a definition-only split, so there are no proof steps or pending theorem nodes. Lean formalization remains a later stage of the project.

## Review by M1

I read the imported item and the parent blueprint node `def-sc-function-field`. I checked the source copy of Stacks Morphisms Section 29.49 in `/home/ubuntu/c1-stacks-review/morphisms.tex`: Definition 01RS (rational maps, including the dense-open equivalence relation), Definition 01RT (rational functions as maps to the affine line), and Definition 01RU (the ring structure), together with the section description in the proof of Lemma 01RV and Example 01JH (global sections). The node’s section-based presentation is exactly the identification used there: a representative is a section in `\mathcal O_X(U)`, restriction to a common dense open gives equivalence, and intersection of dense opens supplies the operations. The node’s only statement dependency is `[def-pc-scheme]`, whose statement explicitly introduces schemes and open subschemes; no other imported node is needed to state this definition.

There are no proof steps for a definition, so there are no cited step claims or hidden non-elementary arguments to validate. I nevertheless checked the defining edge cases: dense opens have dense intersection by the open-set argument; the equivalence relation is transitive after intersecting the two witness opens; the empty scheme and disconnected schemes use the same definitions; and nilpotents do not alter the section-level construction. I searched the full DAG and `tools/blueprint_refs.py` for rational functions, dense opens, and the item id, finding no duplicate definition or same-as blueprint node. The existing Mathlib searches were checked: LeanSearch, LeanFinder, Loogle, and a source grep find `Scheme.RationalMap` and the irreducible-scheme function field, but no ring of rational functions as a colimit of sections on arbitrary schemes, so there is no Mathlib attachment. Finally, I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, blueprint marker, and rational-function declarations; the source has related uses and RationalMap infrastructure but no exact declaration.
