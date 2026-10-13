## What changed

Proved `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_tensor_coordinates`
in its assigned module, preserving its signature and visibility. Added proof-only imports of
`Sheaf.AlgebraicGeometry.AffineConormalSections`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`, and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`.
The private proved helper `tensorQuotientBijective` derives the needed tensor bijection
from annihilation of the extended kernel ideal and Mathlib tensor right exactness.
Composed this with affine conormal coordinates, tensor swap and scalar cancellation.
The normalized pure-tensor equation follows from the existing conormal unit formula.
Updated the existing node's proof and dependencies to this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_affine_tensor_coordinates`
(node `lem-weil-pbc-closed-immersion-conormal-affine-tensor-coordinates`).
No holes remain in the assigned module; no holes were added or split off.
The private helper is fully proved. This uses the existing affine conormal theorem;
its own remaining dependencies are outside this delivery.
Local compilation completed without errors or warnings.

## No longer needed

No original imports were removed: all four public imports support the statement.
The planned proof dependency `lem-weil-pbc-tensor-over-quotient-ring` is no longer needed
by this proof. Neither `TensorProduct.quotTensorEquivQuotSMul` nor
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, quotient-ring identifications,
or a C-linear upgrade of the conormal equivalence is needed.
That node is a Mathlib leaf and has no Sheaf module to remove.
All other original proof dependencies are retained. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or interface was found. The explicit quotient-tensor calculation
can be shortened: surjectivity and tensor right exactness suffice once the extended
kernel is shown to annihilate the tensor. Edge cases J=0, J=A and zero chart rings
are covered uniformly by the proof; no flatness or nontriviality instance is used.

## Second reading by P4

1. **Interface unchanged — pass.** Compared the complete delivered module with the
   repository version using `diff`, and compared the existing theorem signature
   byte for byte. The signature, visibility, existing docstring and four public
   imports are unchanged. Only the private proved helper, three proof-only imports
   and the theorem proof were added. There are no definition or statement changes
   and no change records are needed.
2. **Proof and trust — pass.** Compiled the delivered module locally without errors
   or warnings. Compiled a scratch copy with `#print axioms` for both
   `tensorQuotientBijective` and
   `closedImmersion_conormal_affine_tensor_coordinates`: both use exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned the
   source: no holes, forbidden declarations, foreign implementations or kernel
   bypasses. The helper proves annihilation of the extended ideal on the tensor,
   then zero range of the tensored kernel inclusion; right exactness and
   surjectivity give bijectivity. The target composes concrete tensor maps and
   uses the existing normalized affine conormal equation. No data definition
   chooses an arbitrary witness from an unproved existence theorem.
3. **Split statements and edge cases — pass.** No statements were split off and
   no holes were added. The private helper is fully proved and strictly an
   algebraic part of the argument. Checked J=0 (q has zero kernel), J=A (the
   annihilation hypothesis forces M=0), zero B or D, and zero M: the proof needs
   no proper ideal, nontrivial ring or flatness hypothesis. Independent Loogle
   and LeanFinder searches using tensor kernels and annihilation, plus `rg` of
   the library and Mathlib tensor modules, found the right-exactness ingredients
   already used, rather than a shorter exact replacement for this helper.
4. **Route and pruning — pass.** The target is proved directly from affine
   conormal sections, the pullback kernel identity, affine ideal comap, and
   Mathlib tensor right exactness and compatible scalar change. Each added
   proof-only import supplies declarations actually used. The original public
   imports support the unchanged statement. Compared the old and new
   `proof_deps`: their sole removed node is
   `lem-weil-pbc-tensor-over-quotient-ring`, already listed under No longer
   needed; it is a Mathlib leaf, so no module is pruned. Read the realized route
   of `dag/units/sk-thm-p1.json`: no realized unit statement or step is bypassed
   or changed by this local algebraic simplification.
5. **DAG agreement — pass.** Compared both node records: only `proof`,
   `proof_deps` and `proof_origin` change. Read every retained dependency's Lean
   or Mathlib record and the four new proof steps against the code. They record
   the kernel calculation, annihilation, right-exactness bijection, compatible
   scalar change and pure-tensor normalization accurately. No new public
   statements or new nodes are introduced.

Second reading changed only this report, adding the independent checks above.
The Lean proof and node record needed no repair. Closed one existing hole; added
zero holes; split off zero statements.
