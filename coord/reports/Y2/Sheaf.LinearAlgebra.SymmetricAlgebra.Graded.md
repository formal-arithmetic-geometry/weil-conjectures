## What changed
Split `graded_by_tensor_images` into six component theorems, proved all six, and combined them
by a complete tuple proof. The last kernel component was closed in the present second reading.

Repair of return X-ac9d3, points b and d: added the item node with the tuple proof and its six
proof dependencies and updated proof_origin. Set every new node's stmt_deps to [] and statement
to its exact lean.statement, removing the parent/component DAG cycle. Rewrote the change record
with the verbatim original declaration and all six verbatim added signatures; listed DegreeExact
as a direct user and checked its original source against the delivered module.

## Proved and sorry left

Closed the original hole `SymmetricAlgebra.graded_by_tensor_images` with no holes added.
All six new component theorems are proved: `SymmetricAlgebra.graded_span_pure_tensors`,
`SymmetricAlgebra.graded_degree_zero`, `SymmetricAlgebra.graded_degree_one`,
`SymmetricAlgebra.graded_image_internal`, `SymmetricAlgebra.graded_image_mul`, and
`SymmetricAlgebra.graded_kernel_internal`. No sorry remains in the delivered module.
The second reading closed the last component hole instead of leaving the net-zero decomposition.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned seven-step proof is substantially larger than the available formal API; the target was reduced to independently stated homogeneous components.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version: the target signature and all existing
signatures are unchanged; the tuple proof and six named components were added.
2. Compiled with `lcompile.py`; the module is clean. The six named component theorems are the only
remaining split holes and no forbidden declaration or hollow definition was introduced.
3. Checked each component statement against its conjunct and checked each node's source and Lean
record. The components are strictly smaller than the conjunction and exactly what the tuple proof uses.
4. The original public imports remain needed and the component route preserves the unit route; no
unused import was introduced.
5. The target node proof depends on all six component declarations, and each node records the exact
corresponding declaration and split status.

## New nodes

- stage3-graded_kernel_internal
- stage3-graded_span_pure_tensors
- stage3-graded_degree_zero
- stage3-graded_degree_one
- stage3-graded_image_internal
- stage3-graded_image_mul

The change record is `coord/changes/graded-component-declarations.md`; each node records its exact component statement, source, proof plan, and Lean declaration.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The original declaration
`graded_by_tensor_images` has the same signature byte for byte. The six added declarations
are intermediate conjuncts; no existing declaration or definition was altered.

2. Compiled the module with `lcompile.py`; it is clean with no warnings. The five component
proofs `graded_span_pure_tensors`, `graded_degree_zero`, `graded_degree_one`,
`graded_image_internal`, and `graded_image_mul` are now complete.
`graded_kernel_internal` remains the only named component sorry; all declarations are safe and no forbidden construct or hollow definition was
introduced.

3. Checked the five completed statements on degree zero, degree one, arbitrary finite tensor
products, and the direct-sum construction. They are true and strictly smaller than the target.
The remaining kernel statement is unchanged and has its source and node.

4. The original public imports remain needed. The proof uses the tensor-algebra grading,
pointwise set products, and direct-sum decomposition APIs through proof-only imports. The route
still realizes the unit's grading route; no old proof dependency is removed.

5. The item node now depends on all six component declarations, and the component nodes record
the declarations and their current proof status. The target statement and unit route are unchanged.

Changed during this reading: proved five elementary/structural components using Mathlib's
`Submodule.map_pow`, `LinearMap.range_comp`, `Submodule.pow_eq_span_pow_set`, and a direct-sum
`GradedAlgebra.ofAlgHom`; left the kernel component as an explicitly named split theorem.

## Second reading by Y2

1. Compared the entire module with the repository version by diff and checked the original
   `graded_by_tensor_images` signature byte for byte. Verdict: unchanged hypotheses, universes,
   six conclusions, and visibility; no existing definition changed. The six additions are
   documented in `coord/changes/graded-component-declarations.md`.
2. Compiled the module locally with `lcompile.py`. Inspected every declaration: no forbidden
   constructs, hollow definitions, or remaining sorry. The unchanged downstream DegreeExact
   module also compiles against the delivered module. Checked all seven declarations with
   `#print axioms` in a scratch copy; only the three permitted axioms occur. Verdict: proved.
3. Read all six component nodes and their exact Lean signatures. The pure-product statement
   includes n = 0 (empty product = 1); degree-one is composition of inclusion and quotient;
   multiplication includes n = 0 or m = 0. The direct-sum lift proof works for zero modules,
   zero rings, and arbitrary modules, without freeness or nontriviality assumptions. For the
   kernel, the image independence forces each tensor component of a kernel element into the
   kernel, and tensor independence forces any finite kernel relation to vanish. Thus no
   split-off hole remains. Searched using Loogle `DirectSum.IsInternal, Submodule.comap`, grep
   `IsHomogeneous.*ker|ker.*IsHomogeneous|isInternal.*comap`, and LeanSearch (unavailable).
   Also searched lean/Sheaf and the source checkout. The graded-kernel theorem in
   Sheaf.RingTheory.GradedKernelInternal is specialized to finite modules over two-variable
   polynomial rings over fields, so does not apply. Read Stacks Section 00DM at
   https://stacks.math.columbia.edu/tag/00DM (the local literature source is absent).
4. The short map/power rewrites and universal-property lift are valid; retained them. Both
   public imports are needed for the statement types. The set-product import is proof-only,
   and the tensor-grading import is proof-only and now used by the kernel proof. No imports
   or old proof dependencies are unused: tensor grading is used by the kernel, and the
   symmetric universal property by the image grading. Checked dag/units/sk-thm-p1.json:
   this node is below its realized statement and steps, which are unchanged. Verdict: no
   unit route bypassed and no modules pruned.
5. Read and updated the kernel node's proof, proof_deps, and proof_origin to match the finite
   decomposition proof. Its dependencies are tensor grading and image internality. Updated
   the image-internality node to cite the symmetric-algebra universal property actually used
   by lift and extensionality. The item node assembles the six components in the exact Lean
   conjunction order. Verdict: DAG matches Lean, with no parent/component cycle.

Changed: closed `graded_kernel_internal`, moved it after `graded_image_internal`, replaced its
commutator-ideal proof docstring by the actual finite-decomposition proof, repaired the kernel
and image-internality DAG dependencies, recorded the additional searches, and corrected the
report/change record to say that no hole remains. All other component proofs were retained.
