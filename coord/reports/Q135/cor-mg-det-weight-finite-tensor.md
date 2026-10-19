## Files written

- `dag/nodes/sec-purity-real-sheaves/cor-mg-det-weight-finite-tensor.json`: statement, existing dependencies, split proof; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every dependency used by every proof step.

## Attachments

None. I searched the slopmaster2 WeilConjectures tree for the item id, its title, and determinant-weight tensor declarations; no sorry-free project declaration states this item exactly.

## WANTED

None.

## Source error

None found. The current main-20261015 statement and proof agree with the imported master statement; the tensor rule's finite-determinant hypotheses are supplied by `lem-rp-determinant-weights-agree` for every nonzero lisse constituent.

## Review by Q135

I read the item in `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-detweights/cor-mg-det-weight-finite-tensor.md` and its proof file, then compared them with the imported master node and with the unit `sk-d-real-detweights`. The item statement is unchanged: it assumes a nonzero lisse Weil sheaf with semisimple geometric representation on a normal geometrically connected curve, uses one determinant-weight entry per occurrence of a simple composition factor, and asserts exactly the sum description and the maximum `kβ`. I also read the source definitions of Weil-representation operations and determinant-weight multiset.

For step 1, I opened `def-mg-weil-composition-series`, `lem-mg-jordan-holder`, `def-mg-determinantal-weight-multiset`, `lem-rp-determinant-weights-agree`, and `def-wf-determinantal-weight`. I also opened `lem-mg-composition-series-exists`, which explicitly supplies the composition series rather than treating its definition as existence. They state respectively what a composition series and its factors are, Jordan–Hölder invariance with multiplicity, the multiset entries, finite geometric determinant plus agreement of the two weight notions for nonzero lisse sheaves, and the determinantal-weight notation. These statements justify reindexing `α_i` to the simple factors and the finite-determinant hypotheses. The imported citation of geometric semisimplicity was unused and was removed.

For step 2, I read `def-real-weil-representation-operations` and the same composition-series and multiset statements. They say that constituents are composition factors counted with multiplicity, so the `k=1` base case is exactly the chosen factors and their previously identified weights. For step 3, I read the full statement of `prop-ag-det-weight-two-factor-tensor`: it applies to nonzero lisse sheaves, requires finite geometric determinants for both factor series and the tensor constituents, and gives the forward equality for every tensor constituent. I checked each of those hypotheses for `F_0^(⊗(k-1))`, `F_0`, and `F_0^(⊗k)` using step 1 for finite determinants. I wrote out nonzeroness of tensor powers using functionals evaluating a pure tensor to 1, and continuity using products of matrix coefficients; composition-series existence is explicitly cited again. These are representations of the same Weil group throughout, so there is no change of base curve or coefficient category. For step 4, I checked the proposition's explicit converse clause and then the elementary real-number bound by `β`; nonzeroness ensures the finite list of `α_i` is nonempty.

I tested the statement on `k=1`, on a rank-one sheaf, on a direct sum of two simple factors with equal weights, and on a nonsplit extension with the same composition factors. In each case the list retains composition-factor occurrences and the tensor-power weight set and maximum agree; the item asserts occurrence of sums, not a formula for their multiplicities. The tensor rule in the other chapter is a general tool already marked Lean-closed in the current DAG; composition-series existence and Jordan–Hölder are likewise already closed tools. No new route or tool declaration is required. I searched the whole DAG and blueprint using `blueprint_refs.py search` for determinant weights and tensor powers; the exterior rule is different and the two-factor tensor proposition is strictly shorter than this induction. Six Mathlib searches were run through msearch.py, all successful: LeanSearch, Loogle, two LeanFinder phrasings and two grep patterns. I read the hits: LieModule eigenweights, tensor-action definitions, ordinary characters, whole-tensor determinants and tensor-power associativity do not state this item. No service was unavailable.

The four proof steps are each below the long-step review threshold and expose the induction rather than hiding it in one paragraph. I corrected initially paraphrased citation excerpts by copying exact statement text, including TeX and newlines. Every citation in `citations.json` is a verbatim excerpt from the corresponding node statement. No new node was created because all non-elementary facts used by the proof are already represented by the cited DAG nodes.

## What could not be finished

Nothing.
