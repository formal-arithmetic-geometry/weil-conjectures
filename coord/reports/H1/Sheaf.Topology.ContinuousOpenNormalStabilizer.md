## What changed

Replaced the sorry proof of `ProfiniteGrp.exists_openNormalSubgroup_right_invariant` with a
compactness argument. For each point, the Mathlib open-normal-neighborhood theorem gives an
open normal subgroup inside the fibre translate; compactness yields a finite cover, and the
finite infimum of the corresponding subgroups gives the required invariant subgroup. Added the
proof-only import `Mathlib.Topology.Algebra.ClopenNhdofOne`. The second reader updated the
existing node's `proof` and `proof_origin` to describe this direct normal-neighbourhood route.

## Proved and sorry left

The declaration `ProfiniteGrp.exists_openNormalSubgroup_right_invariant` is proved. No `sorry`
remains in the delivered module and no new nodes or sorries were added. Holes closed: 1,
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant`; holes added: 0. This is a proof,
not a decomposition.

## No longer needed

No stated DAG dependencies were removed; the node has no proof dependencies. The proof uses only
Mathlib declarations and does not require any additional Sheaf modules.

## Where the brief, the DAG or earlier work was wrong

Nothing identified.

## Second reading by H1

1. Compared the only delivered Lean module with the repository using `diff -u`. The existing
   theorem signature, namespace, universes, visibility and docstrings are byte for byte unchanged.
   Only the proof and one plain proof-only import differ; no definitions or change records.
   Verdict: pass.
2. Compiled the delivered file locally through `lcompile.py`, with no errors or warnings.
   A scratch copy with `#print axioms ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry remains, no forbidden
   declarations occur and no data is obtained from an unproved existence theorem. Verdict: pass.
3. No statements were split off and no new declarations or nodes were added. Checked small cases:
   the trivial group and constant functions fit the argument; an empty codomain admits no map
   from a group. The finite cover is nonempty because it covers the identity, so the use of
   `Finset.inf'` is justified. Verdict: pass.
4. Read the Mathlib neighbourhood theorem and searched with Loogle `ProfiniteGrp, Continuous`
   and ripgrep for right invariance, quotient factorization and open-normal subgroups in Mathlib
   and both library roots. No shorter exact theorem was identified. The proof directly uses
   Mathlib's normal neighbourhood basis, compactness and a finite intersection; it introduces
   no lower holes. The two public imports supply the theorem's signature; the new import is
   plain because only the proof needs it. There were no old proof dependencies to prune.
   Read `dag/units/sk-prop-h2.json`: this node realizes none of its statement or steps, and the
   unit's recorded route is preserved. Verdict: pass.
5. The original node described an extra finite-index normal-core step absent from the Lean.
   Updated its `proof` and `proof_origin` to the actual normal neighbourhood / finite cover /
   finite infimum argument. `proof_deps` remains empty, matching the Mathlib-only proof.
   No new-node fields or statement changes are needed. Verdict after repair: pass.

Second-reading changes: repaired DAG proof-route metadata and made the report's hole accounting
explicit; the Lean proof was correct and was left unchanged.
