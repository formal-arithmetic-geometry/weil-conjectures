## What changed

Split the unresolved positive-rank and rank-zero determinant calculations into two public
intermediate theorems, each in its own module, and imported them into the parent module.
The parent theorem is now proved by a real by_cases reduction on r = 0.

## Proved and sorry left

Proved ExteriorAlgebra.koszul_conormal_comparison_isIso_top_homology.
The strictly simpler intermediate declarations
koszul_conormal_comparison_isIso_top_homology_pos and
koszul_conormal_comparison_isIso_top_homology_zero remain sorry, with nodes
lem-sc-koszul-conormal-top-homology-pos and
lem-sc-koszul-conormal-top-homology-zero.

## No longer needed

None of the parent proof dependencies were removed; the parent calculation is represented by the
two split nodes above.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the parent theorem itself as sorry and did not provide DAG nodes for its
two intermediate declarations, so the delivery tool could not accept the unresolved holes.

## New nodes

lem-sc-koszul-conormal-top-homology-pos and lem-sc-koszul-conormal-top-homology-zero, matching the
two intermediate modules in this delivery.

## Earlier second reading (a previous round; superseded)

The parent reduction is unchanged and the two intermediate statements are strictly simpler
positive-rank and rank-zero cases. Their remaining proofs are the explicit determinant calculations
recorded in their docstrings and nodes.

## Second reading by F4

1. I compared the delivered parent module with the repository version. The theorem signature is
   unchanged; the only parent changes are the proof and proof-only imports of the two split modules.
   Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py`. The parent proof is a genuine case
   split on `r = 0`; the two remaining `sorry`s occur only in the named public intermediate
   theorems. Verdict: pass.
3. I checked both split statements against their Lean declarations and their DAG nodes. They are
   the positive-rank and rank-zero special cases of the unchanged target, with the same hypotheses
   and conclusion, and their docstrings record the determinant calculation and source. Verdict:
   pass; the decomposition is mathematically true and strictly simpler than the parent.
4. I checked the imports and proof route. The parent uses the split declarations directly, while
   each split module publicly imports only `KoszulConormalComparison`, which supplies its public
   statement types. No old proof dependency is removed and the unit route remains represented by
   the parent node. Verdict: pass.
5. I checked the DAG node metadata, declarations, statements, sources, proof dependencies, and
   blueprint/unit references. The two new nodes match the two new modules and the parent node's
   proof now records the case reduction. Verdict: pass.

I restored a concise explanatory docstring on the parent theorem, added this second-reading record,
and made no mathematical or interface changes. The two determinant calculations remain split-off
`sorry` theorems with their corresponding nodes.
