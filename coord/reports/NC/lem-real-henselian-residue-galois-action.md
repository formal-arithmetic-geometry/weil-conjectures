Files written:
- `dag/nodes/sec-purity-real-sheaves/lem-real-henselian-residue-galois-action.json`: statement, split proof, main-20261015 blueprint binding; no new node.
- `citations.json`: verbatim citations for every non-elementary step.

Attachments: none.

WANTED: none.

The item has no finished declaration in `WeilConjectures/` in slopmaster2 and no exact declaration in the upstream reference checkout. I searched the whole DAG and both blueprint snapshots for the item, its Stacks tags, and the locality/residue/Galois keywords. The only close material is the existing generic finite-over-henselian product node and the existing integral-extension nodes, which are cited as tools rather than duplicated. The old imported source place had already been normalized to Tags 04GH and 00GN; the proof follows the current main-20261015 `d-real-boundary` decomposition-group clause. I corrected the node from `unsplit` to `split`, filled the current blueprint snapshot/place, and supplied the missing proof dependencies and tool-use declarations. No statement dispute was found.

## Not duplicates

`lem-real-henselian-residue-galois-action` vs `lem-weil-pbc-finite-over-henselian-local-product`: the existing node treats one module-finite algebra and gives a finite product decomposition; this item treats the filtered integral closure in an algebraic closure and additionally proves residue algebraic closedness, Galois action, continuity, and constants.

`lem-real-henselian-residue-galois-action` vs `lem-a1-integral-residue-extension-algebraic`: the existing node proves only algebraicity of a residue-field extension for one prime; this item proves the residue ring is an algebraic closure and then adds equivariance.

`lem-real-henselian-residue-galois-action` vs `lem-weil-pbc-integral-maximal-contracts-maximal`: the existing Mathlib leaf is only maximal-ideal contraction under an integral map; it does not assert locality of the integral closure or any Galois statement.

## Review by NC

I read the item node, the current `main-20261015` `d-real-boundary.md`, the older master copy for the imported source, Stacks algebra.tex Tags 04GH and 00GN, and the statements of every cited DAG node. Step 1 uses the definition of integral closure and the finite-adjoin theorem exactly to make each finite subalgebra module-finite. Step 2 applies the cited finite-over-henselian product statement under the stated henselian-local hypotheses; the subalgebra is a domain in `Omega`, so the product has one nonzero factor and gives a local ring whose maximal ideal contracts to `m`. Step 3 writes the local-ring unit criterion for the filtered union. Step 4 uses the cited integral maximal-contraction statement and the fact that `R` is local, verifying the contraction is `m`. Step 5 applies the cited residue-extension algebraicity statement to `n` over `m`. Step 6 checks the algebraic-closedness clause by lifting a monic polynomial, adjoining a root, using finite-implies-integral and transitivity, and returning the root to the defined integral closure; this uses exactly the quoted statements. Step 7 checks that an absolute Galois automorphism fixes the image of `R`, hence preserves `B` and its unique maximal ideal, and that reduction gives the displayed homomorphism. Step 8 checks continuity directly from finite lift representatives and the stated Krull bases. Step 9 verifies constants are integral, reduction is injective, and surjectivity follows because the residue field is algebraic over the finite `kappa` while the image of the algebraic closure `k'` is algebraically closed. Step 10 is the direct reduction formula proving equivariance. I tested the formulation on `R=K` finite, a henselian DVR into its fraction field, a map killing the maximal ideal, and a nonreduced henselian local ring. Every proof step is under the 2000-character long-step threshold. The required leanfinder, Loogle (including a corrected second pattern), grep, and leansearch searches were run and recorded in `searches.jsonl`; no Mathlib declaration states the item.
