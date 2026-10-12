## What changed

Completed both proofs in `lean/Sheaf/LinearAlgebra/ExteriorTopDirectSum.lean`, preserving
all existing signatures, public imports, and docstrings. All added helpers are private
and fully proved. The canonical map is a real construction: exterior-power maps of the
two inclusions followed by homogeneous multiplication and `TensorProduct.lift`.
Its wedge formula follows directly from exterior-algebra multiplication. One-element
top exterior bases and their tensor-product basis prove bijectivity. Tensor and
exterior-power extensionality prove uniqueness and naturality.

Added the proof-only Mathlib import `Mathlib.LinearAlgebra.ExteriorPower.Basis`.
The second reading removed four redundant proof-only imports whose declarations are
already available through the retained imports. Updated the existing
node's proof and proof origin to describe the implemented argument; its dependencies
remain the same. The unit route remains intact.

## Proved and sorry left

Closed both original holes:
- `exteriorPower.existsUnique_topDirectSum` (node `lem-sc-exterior-top-direct-sum`).
- `exteriorPower.topDirectSum_natural` (same node).

No holes added, no holes left, and no dependencies on other project's unproved
statements. This is a proof, not a decomposition. All helper definitions have concrete
data and all helper lemmas are proved. The argument applies uniformly to ranks zero,
the zero ring, and characteristic two; no nontriviality assumption is used.

## No longer needed

No repository imports, nodes, or modules pruned. Removed the redundant added imports
`Mathlib.LinearAlgebra.ExteriorAlgebra.Grading`,
`Mathlib.LinearAlgebra.TensorProduct.Basis`, `Mathlib.LinearAlgebra.Basis.Prod`, and
`Mathlib.Order.Preorder.Finite`; compilation succeeds without all four together. The two planned basis nodes are used
through their recorded Mathlib matches. The previous sandbox's existence and uniqueness
placeholder nodes and holed helpers were discarded; neither is needed by this proof.
They were unlanded drafts, not repository pruning.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at spanning, although Mathlib's `TensorProduct.ext` and
`exteriorPower.linearMap_ext` directly implement the needed argument. Its two placeholder
nodes lacked real statements, proof plans, and search records. This delivery removes
them rather than moving either hole into a new statement. The DAG's basis route is
sound; homogeneous exterior-algebra multiplication makes its arbitrary-wedge formula
immediate and avoids a separate coefficient expansion.

## Second reading by M1

1. **Visible changes.** Compared the delivered module with the repository version. The two public theorem signatures and all existing declarations are byte-for-byte unchanged. The only additions are private proof helpers and one retained plain proof-only Mathlib import; the DAG node changes only its proof route and origin as reported.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is clean and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch compilation of both public theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and duplication.** Checked both target statements against the repository and tested the construction at ranks zero and one, including the zero-ring and characteristic-two cases. The private helpers are concrete constructions, and no split-off statements or new public nodes were added. Searches found no existing declaration duplicating either theorem.

4. **Route and pruning.** The proof follows the unit route: graded multiplication, one-element exterior-power bases, tensor/product bases, then extensionality for uniqueness and naturality. Both planned basis dependencies are used through their Mathlib matches. Four added proof-only imports were redundant and removed; no repository import, module or node was pruned.

5. **DAG agreement.** The node proof steps describe the implemented construction and basis identification, while `proof_deps` and `proof_origin` remain consistent with the declarations used. The unit record's `realized` arrays are currently empty; this pre-existing metadata gap is unchanged. The proof retains the planned determinant basis route and bypasses no unit.

I removed four redundant proof-only imports and corrected the report, including adding this second-reading record. I left the proof implementation unchanged. No holes were added; both original theorem holes are closed.
