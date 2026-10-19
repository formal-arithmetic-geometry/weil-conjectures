# Stage-1 report: lem-kun-03qu-global-generation

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-03qu-global-generation.json`: item split; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every citation in every proof step.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` states this item exactly.

## WANTED:

None.

## What was wrong in the imported node

The imported proof says that the global-sections/stalk comparison follows from `lem-kun-03qu-sep-closed`, but that node's statement only gives vanishing of higher cohomology and does not state the stalk comparison. I repaired this by citing the existing generic node `lem-weil-pbc-strictly-henselian-sections-stalk`, whose statement specializes to `Spec K` because a separably closed field is a strictly henselian local ring. The rest of the argument is then the evaluation-map calculation followed by exactness and conservativity of geometric stalks.

## Review by N0

I read the item, its unit `sk-prop-sf-kunneth-ordinary`, the chapter record, and the source blueprint proof. I searched the whole source tree for the item tag and global-generation declarations; the only relevant sorry-free source declaration is the module theorem for a different `IsGloballyGenerated` notion in the old reference checkout, and no declaration in the required slopmaster2 source states this abelian-sheaf item. I read the statements of `def-kun-global-generated`, `def-kun-separably-closed`, `def-weil-pbc-henselian-terminology`, `lem-weil-pbc-strictly-henselian-sections-stalk`, `prop-weil-pbc-geometric-stalks-exact`, and `lemma-weil-pbc-geometric-stalk-conservative`. Step 1 verifies the hypotheses for the strict-henselian specialization: the zero maximal ideal makes the henselian pair immediate and the residue field is the separably closed K. Step 2 uses exactly the evaluation morphism defined by `def-kun-global-generated`; after the cited germ isomorphism, its stalk is the free abelian-group map sending a basis element to its indexed section, which is visibly surjective, including the zero group case. Step 3 uses the exact stalk statement to identify cokernel stalks and the conservative stalk statement to conclude the cokernel vanishes, then invokes the definition of global generation. I checked the empty/zero sheaf and a constant sheaf as small cases. I also ran the required LeanFinder, Loogle, grep, and LeanSearch Mathlib searches; LeanSearch was unavailable and is recorded as such. No new node was needed, and the off-unit strict-henselian lemma is declared as a generic tool use in the split report.

## What could not be finished

Nothing; the dry run printed `OK (not pushed) ... preflight passed`.

## Second reading by N0

- Item statement: checked against the blueprint node and the separably closed-field/global-generation clauses; added explicit citations for the separably closed field, abelian sheaf, and small étale-site notions.
- Step 1: checked against Stacks Tag 03QO (lemma-vanishing-etale-cohomology-strictly-henselian), including the strictly henselian specialization to the field K; the cited strict-henselian sections/stalk statement supplies exactly the comparison used.
- Step 2: checked against the evaluation-morphism definition and the germ isomorphism; the stalk map is the basis-element map and is surjective, including the zero-group case.
- Step 3: checked the stalkwise surjectivity conclusion against the existing generic node lem-kun-global-generated-stalkwise; exactness/conservativity were already encapsulated by that node, so the duplicate argument was removed and its verbatim citation was added.
- New nodes: none; no new-node form or Mathlib-leaf review applies.
- Changes: repaired the item statement dependencies and citations, replaced the repeated exactness/conservativity conclusion with the existing stalkwise criterion, updated citations.json, and recorded this second reading.
- Small cases checked: the zero sheaf and a constant abelian sheaf on Spec(K), with the empty direct sum and the basis-vector evaluation map behaving as stated.
