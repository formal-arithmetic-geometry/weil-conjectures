# Stage 1 report: lem-coef-tree-zigzag-finite-subtree-colimit

## Files written

- `dag/nodes/sec-six-functors/lem-coef-tree-zigzag-finite-subtree-colimit.json`: split statement; no new child nodes.
- `citations.json`: verbatim proof-step citations.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures` states this item.

## WANTED

None. The Dwyer--Kan PDF is cited by URL and its Section 5.8(iii) was used as the source; no additional document is needed.

## Not duplicates

No new nodes were created, so there are no duplicate pairs.

## Review by Q92

I read the item node, its chapter and unit records, the imported blueprint ancestry, and the definitions of the relative zigzag nerve and categorical colimit. I searched the entire DAG and the main and slopmaster2 blueprint trees for the item and for finite-subtree/zigzag formulations; no duplicate or more general existing node states this result. I also searched both read-only Lean source trees for the item id and its mathematical key words; no declaration was found. The existing `lem-coef-small-set-colimit-quotient` node was read in full and is used only for its stated representative and equality characterization of a set colimit.

Step 1 verifies that finite connected subtrees containing $x$ form a small nonempty filtered poset: the singleton gives nonemptiness, and the finite union of the unique paths from $x$ gives a finite connected upper bound. Step 2 reads the zigzag definition literally: a nerve simplex is a finite string of finite diagrams and commuting vertical maps, so it has finite vertex/edge support; adjoining paths to $x$ places it in one finite subtree. The identity-horizontal-arrow case has empty additional support. Step 3 checks that subtree inclusions are injective on finite path words and therefore on zigzag morphisms and nerves. Two representatives that agree in the full tree agree in a common finite upper subtree, and the cited set-colimit quotient node supplies exactly the equality relation used by the colimit. Step 4 combines the resulting surjectivity and injectivity degree by degree and checks compatibility with faces and degeneracies, yielding the simplicial-set isomorphism.

I checked the hypotheses that $T$ is small and has finite unique paths, that $x$ is a vertex, that all zigzag words are finite, and that the colimit is degreewise in sets. I corrected the imported unsplit node by supplying the complete proof, adding the existing small-set quotient citation to `proof_deps`, and setting `proof_origin`, `status`, and the blueprint split report. No source error or hidden auxiliary lemma requiring a new node was found; every proof step is under the long-step threshold.

## Source error

None.

## What remains

Nothing for this stage-1 split.
