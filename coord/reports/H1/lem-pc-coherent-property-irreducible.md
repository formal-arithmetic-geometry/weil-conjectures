# Stage 1 report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-coherent-property-irreducible.json` — item, statement split, no new nodes.
- `citations.json` — verbatim citations for all non-elementary step dependencies.

Attachments: none. No new Mathlib leaves.

Tool uses: the three existing Stacks nodes `lem-weil-pbc-coherent-filtration-integral-subschemes`, `lem-weil-pbc-coherent-generic-point-ideal-inclusion`, and `lem-weil-pbc-integral-scheme-ideal-generic-stalk` belong to unit `sk-thm-p1`; they are declared as tools because this unit's route requires their general filtration, generic inclusion, and generic-stalk facts.

WANTED: `literature/stacks-project/coherent.tex`, Lemma 01YH (label `lemma-property-irreducible`), because the project literature checkout does not contain the Stacks source; I read the matching source in `/home/ubuntu/c1-stacks-review/coherent.tex`.

The item was not already proved in `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures`; the keyword and blueprint-tag searches found no declaration. I searched the DAG and blueprint for the item and for the three supporting facts. The existing nodes `lem-weil-pbc-coherent-filtration-integral-subschemes`, `lem-weil-pbc-coherent-generic-point-ideal-inclusion`, and `lem-weil-pbc-integral-scheme-ideal-generic-stalk` state the exact filtration, generic inclusion, and generic ideal-stalk facts used, so I created no duplicate nodes.

## Review by H1

I read Lemma 01YH and its proof at the cited source lines. Step 1 records the elementary extension and filtration induction from the first paragraph. Step 2 uses the existing 01YF filtration statement and checks that every quotient support is a proper irreducible closed subset when the generic point is absent; this is exactly hypothesis (2). Step 3 uses the existing 01YE statement for the injection from a generic ideal and the existing generic-ideal node to identify a nonzero ideal's generic stalk with the function field; the dimension-one hypothesis forces one copy and gives the strict-support cokernel. Step 4 uses the same generic-stalk statement to compare every nonzero subideal and applies hypothesis (1) to its cokernel. Step 5 checks the zero ideal separately, uses the nonzero intersection of ideals on an integral scheme, and derives the contradiction to a bad ideal. Step 6 applies the existing filtration node and Step 1 to arbitrary coherent modules supported in `T`.

For every cited node I opened its statement and copied the relevant sentence into `citations.json`; no step relies on a node's proof. The item itself has no Lean declaration, and the three mandated Mathlib searches were run: LeanFinder returned only unrelated general algebraic-geometry declarations, Loogle returned no hits, grep returned no coherent-sheaf devissage declaration, and LeanSearch was unavailable (recorded as unavailable by the search tool). I checked the edge cases `r=0`, the zero ideal, and an empty filtration explicitly in the split.

## Second reading by H1

- Statement: checked hypothesis-by-hypothesis against Stacks Lemma 01YH (label `lemma-property-irreducible`) in `/home/ubuntu/c1-stacks-review/coherent.tex`; verdict: agrees, including the generic-stalk dimension-one condition and strict-support ideal clause.
- Step 1: checked against the first paragraph of the 01YH proof; verdict: the extension induction and zero case are elementary, with the usual isomorphism invariance of a property.
- Step 2: checked against the second paragraph and the 01YF filtration statement; verdict: repaired to spell out support containment on stalks and why a nonzero ideal on an integral scheme has the full proper irreducible support, with the generic-stalk node cited.
- Step 3: checked against the 01YE application paragraph; verdict: the cited inclusion and generic-stalk statements give `r=1` and nonzero ideal, and the repaired text explicitly derives strict support of the cokernel from stalk exactness and the local isomorphism.
- Step 4: checked against the fourth paragraph of 01YH; verdict: generic stalk comparison and the support argument are valid, with the generic-stalk citation retained.
- Step 5: checked against the ideal-intersection paragraph; verdict: repaired to state that the intersection has generic stalk the function field, and that the quotient has zero generic stalk before applying Step 2.
- Step 6: checked against the final paragraph of 01YH and the filtration statement; verdict: filtration quotients are covered by Steps 2 and 5, then Step 1 applies.
- New nodes: none; the three cited supporting nodes were opened in full, and each citation quotes its statement verbatim. Existing-node and Mathlib searches were checked in the DAG, blueprint, and recorded search log.

Changes: added the missing support and generic-stalk arguments in Steps 2, 3, 4, and 5, and added the corresponding Step 2 citation; no statement or node was created or weakened.
