# Stage 1 report: lem-pc-perfect-generator-pullback

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-perfect-generator-pullback.json`: item marked split with three proof steps; no new nodes and no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every node cited by every step.

## Attachments

None. I searched both project source checkouts for the item tag and for perfect-generator pullback declarations; no sorry-free project declaration states this item.

## WANTED

None.

## Not duplicates

None. The proof uses existing affine derived-adjunction, affine-equivalence, generator-definition, and affine-conservativity nodes; no subordinate statement is introduced.

## Review by F1

I read the imported item and its consumer `lem-sc-proper-flat-right-adjoint-affine-basechange`, then checked the Stacks Project Tag 09IS pullback-generator argument. Step 1 uses the exact Hom bijection in `lem-pc-ringed-spaces-derived-adjoint-general`; I also read `lem-sc-finite-affine-derived-equivalence` to verify that affine `Rg_*` lands in the quasi-coherent derived category and is the restriction of the affine equivalence. Step 2 applies the exact weak-generator definition in `def-pc-generators`; the shift indexing is harmless because the hypothesis ranges over every integer. Step 3 uses the exact conservativity conclusion of `lem-sc-affine-derived-pushforward-conservative` and then restates the same generator criterion. All hypotheses are checked: `g` is affine, `M` is a generator in `D_QCoh(X)`, and `E` is arbitrary in `D_QCoh(X')`. The zero-object edge case is immediate, and for `g = id` the argument reduces to the original generator criterion. The required LeanFinder, Loogle, grep, and unavailable LeanSearch searches were run for the item and recorded in the node. No cited node is a duplicate or a definition standing in for a theorem.

Nothing remains unfinished.

## Second reading by F1

- Item statement: checked hypothesis by hypothesis against Stacks `perfect.tex`, Tag 09IS, `remark-pullback-generator`; the affine specialization with a perfect generator is valid, and the identity and zero-object cases behave as stated.
- Step 1: checked the adjunction statement of `lem-pc-ringed-spaces-derived-adjoint-general` and the affine equivalence/restriction statement of `lem-sc-finite-affine-derived-equivalence`; both supply exactly the displayed quasi-coherent Hom bijection and its typing.
- Step 2: checked `def-pc-generators`; vanishing for every shift forces `Rg_*E = 0` by the definition, with no extra hypothesis.
- Step 3: checked `lem-sc-affine-derived-pushforward-conservative` and `def-pc-generators`; conservativity gives `E = 0`, exactly the generator criterion.
- New nodes: none; all cited facts are existing nodes, and searches found no duplicate or Mathlib declaration for the item.
- Form and metadata: citations are verbatim; the source path was corrected to `perfect.tex`, and `created.item` was corrected to this item.

Changes made: corrected the source document to the file containing Tag 09IS and corrected the item ownership metadata; no proof step or statement change was needed.
