Files written:

- `dag/nodes/sec-picard-framework/lem-sc-finite-free-internal-hom-exact.json`: statement split, no new node, no Mathlib leaf.
- `citations.json`: verbatim citations for Steps 1 and 2.

Attachments: none.

WANTED: none.

What was checked and corrected:

- No existing project declaration carries the blueprint tag or states this exact finite-free internal-Hom result. The item is therefore split rather than attached.
- The item statement was retained. The proof uses the existing `def-pur-sheaf-hom` and `def-weil-sheaf-of-modules-category` nodes; no supporting node duplicates an existing DAG statement.
- The required Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch. LeanFinder returned only unrelated condensed/module declarations; Loogle and grep returned no match; LeanSearch was unavailable and is recorded as unavailable in the item's search log.

## Not duplicates

`lem-sc-finite-free-internal-hom-exact` vs `lem-sc-ext-tensor-exact`: the existing node proves exactness of tensoring by a finite locally free sheaf, whereas this item proves exactness of internal Hom out of a finite free sheaf and its direct-sum identification.

## Review by F1

I read the item's source, Stacks Project `cohomology.tex`, Tag 0GM8 (Lemma 20.51.4, case (2)), and the blueprint ancestor `thm-sc-p1-duality`. The source calculation identifies Hom out of a finite locally free object with a finite direct sum and then preserves the short exact sequence; the item has exactly those hypotheses, including the rank-zero case. I also read `def-pur-sheaf-hom`, whose statement defines the localized sheaf-Hom presheaf, and `def-weil-sheaf-of-modules-category`, whose statement gives the abelian sheaf-of-modules category and sectionwise kernels/cokernels.

Step 1 uses only the sheaf-Hom definition: precomposition with the selected isomorphism `E \\cong O_U^{\\oplus r}` gives the coordinatewise Hom identification, and the construction is restriction-compatible. The cited node says precisely that sheaf Hom is formed objectwise as Hom on localized sites. Step 2 uses the cited abelian-category statement: the induced maps are coordinatewise postcomposition maps, and finite direct sums of a short exact sequence are exact coordinatewise. Step 3 is transport of exactness and uses no additional node. The hypotheses were checked in the item itself: a ringed site, an `O_U`-module `E`, a chosen finite-free isomorphism, and a short exact sequence in the sheaf module category. I tested `r=0` (all three Hom sheaves are zero), `r=1` (the sequence is unchanged), and a split sequence with `r=2`; each gives the stated result.

No new node was created, so there are no new-node statements or Mathlib leaves to review. The blueprint `from.place` and `same_as` fields were checked and the split report records the parenthetical finite-free Hom calculation it realizes.

What could not be finished: nothing; the dry run is the remaining verification step.

## Second reading by F1

- Statement: checked the ringed-site hypotheses and finite-free rank-zero/rank-one cases against Stacks Tag 0GM8 and the cited sheaf-module definitions; corrected the citation from the unrelated locally-ringed-space-morphism definition.
- Step 1: checked restriction to localized sites and precomposition with the chosen finite-free isomorphism against `def-pur-sheaf-hom`; verdict: valid, elementary.
- Step 2: checked postcomposition maps and coordinatewise finite direct sums against `def-weil-sheaf-of-modules-category`; verdict: valid, elementary, including `r=0`.
- Step 3: checked the commutative comparison diagram and exactness transfer; verdict: valid after making the previously implicit argument explicit.
- Existing nodes: checked `def-pur-sheaf-hom` and `def-weil-sheaf-of-modules-category` statements directly; no new nodes or Mathlib leaves exist.

Changes made: replaced the incorrect `def-weil-locally-ringed-space-morphism` dependency with `def-pur-sheaf-hom` and an explicit ringed-site formulation; rewrote Step 3 to expand the implicit comparison argument; retained the worker's source and search records.
