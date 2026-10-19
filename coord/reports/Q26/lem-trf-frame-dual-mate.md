# Q26: lem-trf-frame-dual-mate

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-frame-dual-mate.json`: existing statement, now split in four elementary proof steps; statement and hypotheses unchanged.
- `citations.json`: empty because no proof step cites another DAG node.
- `searches.jsonl`: required Mathlib searches, including the retained exploratory queries rerun in this sandbox.
- No new nodes, Mathlib leaves, unit edits, Lean edits, or compiler/build operations.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `/home/ubuntu/weil-newtargets-master/WeilConjectures/` for the exact item id, the title, and the dual-mate/evaluation formulas. No declaration states this item exactly; generic Mathlib rigid-category and module-dual declarations do not cover bounded cochain complexes over an arbitrary commutative ring with the stated finite-frame conventions.

## WANTED

None. The proof is agent-origin and follows the final two sentences of the named blueprint proof.

## Corrections and limitations

No `STATEMENT-DISPUTED`: the statement is well-typed and true as written. No hypotheses or conclusions were changed. No new node was needed: each argument is a direct computation from the explicit definitions, the chain-map equation for `f`, and the finite dual-frame identities already present in the item. There are no duplicate-node pairs to report.

## Not duplicates

No new nodes were created, so there are no duplicate comparisons.

## Review by Q26

I read the current item, its chapter and unit records, the ancestor proof `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-p-trace/sk-p-trace.proof.md`, and the existing `lem-trf-chain-supertrace` statement that consumes this lemma. I also checked the exact declaration search in both read-only source trees. The item remains in unit `sk-p-trace`; its source says that the final transported-duality sentence identifies the maps on duals, and the split expands precisely that sentence.

Step 1 checks the degree signs in the dual differential on a homogeneous `x` and uses only that `f` is a degree-zero chain map. It proves that precomposition has the required degree and commutes with differentials. Step 2 evaluates both sides of the mate equation on homogeneous pure tensors; both are exactly `φ(f x)`, while all other total degrees vanish by the stated evaluation convention. Canonical associators and unitors only reparenthesize these tensors.

Step 3 uses the same pointwise evaluation equation to show uniqueness: for every degree `j`, `u φ` and `φ ∘ f` agree on all of `P^{-j}`, so the degree-`j` functionals are equal. Step 4 reads both coevaluation composites at `1`. Expanding `f(e^P_{i,a})` in the `R^i` frame and expanding `ε^R_{i,b} ∘ f` in the `P^i` frame produce the same finite double sum. Equality at `1` suffices for maps from `A[0]`.

All four steps are under 2000 characters and are marked elementary; no cited node is used, so `citations.json` is correctly empty and `proof_deps` is empty. I checked zero terms/empty frames and degree-zero complexes as edge cases. Mathlib searches were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep; the hits concern generic finite-dimensional or rigid-category constructions and do not state this arbitrary-ring cochain-complex assertion. No SGA source is used.

## What was unfinished

Nothing remains unfinished in this one-level split; the required dry run is the remaining delivery check.
