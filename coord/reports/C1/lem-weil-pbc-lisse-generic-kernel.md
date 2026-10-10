Files written:

- `lem-weil-pbc-lisse-generic-kernel.json`: item split; no new nodes; no Mathlib leaf.
- `citations.json`: verbatim statement quotes for all cited nodes in both proof steps.

Attachments: none.

WANTED: none.

No source or statement error was found. The imported proof had incomplete citations: its first step used exactness and conservativity of geometric stalks without naming their existing nodes, and its second step used the stalk definition while citing only the openness lemma. I repaired those uses and made the item status `split`; no new node was needed because `lem-weil-pbc-flat-lfp-open`, `lemma-weil-pbc-geometric-stalk-conservative`, and `prop-weil-pbc-geometric-stalks-exact` already state the required facts.

## Review by C1

I read the item node and the unit `sk-prop-sf-cbc`, and checked the corresponding blueprint proof. I also searched the slopmaster2 source for the item tag and its mathematical keywords; no declaration states this lemma. The first proof step forms the kernel, uses exactness of geometric stalks to identify its generic stalk as zero, and uses the existing conservativity statement to obtain a nonzero germ when the kernel is nonzero. The etale-sheaf definition supplies the local-section and sheaf context. The second step applies the existing flat locally-finite-presentation openness statement to the etale map, then uses the geometric-stalk definition and exactness to choose a geometric point over the generic point and obtain the contradiction. I opened each cited node and verified that its quoted statement says exactly the fact used. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item; the first three found no exact Mathlib match and LeanSearch reported unavailable. Small cases such as `F=0` and an identity map are consistent with the statement.

## Second reading by C1

- Statement: checked against blueprint node `lem-weil-pbc-lisse-generic-kernel` and its stated hypotheses; the zero sheaf and identity-map cases are consistent.
- Step 1: checked against `prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`, and `def-weil-pbc-etale-sheaves`; the kernel and nonzero-germ deductions are supported.
- Step 2: checked against `lem-weil-pbc-flat-lfp-open`, `lem-weil-pbc-inverse-image-stalk-germ`, and `def-weil-pbc-geometric-stalks`; the pullback stalk identification supplies the previously implicit restriction argument.
- New nodes: none; existing-node search covered the exactness, conservativity, openness, and inverse-image-stalk facts.
- Changed step 2 to cite `lem-weil-pbc-inverse-image-stalk-germ` and removed the unnecessary exactness citation there; updated `citations.json` with its verbatim statement quote.
