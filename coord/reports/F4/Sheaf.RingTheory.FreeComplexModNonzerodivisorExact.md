## What changed

Proved `free_complex_mod_nonzerodivisor_exact` in its original module and with its
original signature. Added the proved private helper `lift_reduced_cycle`: lift a
reduced cycle, divide its differential by x, cancel x after applying the next
matrix, and subtract x times a boundary preimage. The main proof uses this helper
for endpoint injectivity and interior exactness. Updated the parent node's proof,
proof dependencies, and proof origin to match this coordinate argument for Tag
00MZ. The second reading replaces the broad matrix imports with direct
statement dependencies; the theorem signature is preserved.

## Proved and sorry left

Closed the one original hole, `free_complex_mod_nonzerodivisor_exact` (node
`lem-weil-pbc-free-complex-mod-nonzerodivisor-exact`). Added zero holes. No sorry
remains in the delivered module. `lift_reduced_cycle` is proved, private, and
introduces no public interface. The earlier attempt's two unproved public split
declarations are removed; they never entered the library.

## No longer needed

Removed `Mathlib.LinearAlgebra.Matrix.ToLin` and the redundant explicit
`Mathlib.LinearAlgebra.Matrix.Defs` import. Replaced them with public imports of
`Mathlib.Data.Matrix.Mul` (the statement uses `mulVec`) and
`Mathlib.RingTheory.Ideal.Quotient.Basic` (the statement uses the ideal quotient).
No proof-only import is public. No Sheaf module is claimed pruned from the entire
target closure.
The proof no longer needs any of the original planned categorical or freeness
proof dependencies:

- `lem-weil-pbc-complex-ses-homology-long-exact`
  (`Mathlib.Algebra.Homology.HomologySequence`).
- `lem-weil-pbc-ring-modules-enough-injectives`
  (`Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`, and its abelian-category
  and mono/injective clauses).
- `def-weil-pbc-exact-sequence` as a categorical proof tool
  (`Mathlib.Algebra.Homology.ExactSequence`); the elementary `Function.Exact`
  interface remains in the statement and proof.
- `def-weil-pbc-free-module` as a proof tool
  (`Mathlib.LinearAlgebra.FreeModule.Basic`); coordinate vectors suffice.
- `def-weil-matrix` as a separate proof dependency; `Matrix` remains a statement
  dependency, supplied by the unchanged public imports.

Removed the earlier sandbox's proposed nodes
`lem-weil-pbc-free-complex-mod-nonzerodivisor-exact-injective` and
`lem-weil-pbc-free-complex-mod-nonzerodivisor-exact-interior`; neither new module
nor new node is needed. This records pruning of this node's proof route, without
claiming that these Mathlib modules leave the entire targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt put two new sorry declarations in the parent module, gave
both the parent's blueprint tag, omitted complete natural-language proofs, and
made their proof dependencies point back to the parent theorem. Its report also
prematurely filled the second-reader section and its change record described no
interface change. All of those artifacts have been removed. The earlier reported
signature mismatch is avoided by using no new split declarations or nodes.

The DAG's homology route is mathematically sound but unnecessary for this matrix
statement. The direct proof is its elementary cycle chase; no unit-level route
is bypassed (this node is not in `sk-thm-p1.realized`). Locality and maximal-ideal
membership are unused, as the existing node already notes, and remain in the
signature. Zero ranks and the endpoint case e=2 require no additional hypothesis.

Validation: the whole delivered module compiles using the required local compiler.
The quotient lifts use surjectivity proved in Mathlib; no data is chosen from an
unproved theorem. The required delivery dry run checks declarations' axioms.


## Second reading by F4

1. **Unchanged interface: PASS.** Compared the sole delivered module with the
   repository using `diff -u` and checked the complete existing theorem signature
   byte for byte by script. It is identical, including all hypotheses, both
   conclusions, universe and visibility. There are no changed definitions; the import cleanup is recorded in
   `coord/changes/free_complex_mod_nonzerodivisor_exact-imports.md`. The only
   added declaration is a private proved helper.
2. **Proof and axioms: PASS.** Compiled the original delivery and the repaired
   imports with `lcompile.py`, with no errors or warnings. A scratch copy with
   `#print axioms` for both `free_complex_mod_nonzerodivisor_exact` and
   `lift_reduced_cycle` reports exactly `propext`, `Classical.choice`, and
   `Quot.sound`. Scanned for sorry and forbidden declarations: none. Quotient
   representatives are chosen using Mathlib's proved surjectivity, and the
   corrected cycle is constructed explicitly as `w - x • z`.
3. **Split statements: PASS (none).** There are no split-off statements, new
   public statements, new nodes, or new holes to assess. Checked the helper's
   cycle chase: divisibility follows from the quotient kernel; exactness gives
   the composite zero and the boundary preimage; nonzerodivisor cancellation
   takes place coordinatewise. Zero ranks cause no inhabitedness assumption.
   At `e = 2`, only endpoint injectivity is requested, and the lift uses precisely
   exactness at degree 1. Reviewed the source statement and proof at
   [Stacks Tag 00MZ](https://stacks.math.columbia.edu/tag/00MZ), since the local
   literature checkout is absent on this machine.
4. **Shortest route, imports, pruning and unit: PASS after import repair.**
   Searched the local library under the theorem and module names and ran
   `msearch.py ... grep` using cycle lifting, four-term exactness and
   nonzerodivisor keywords. Read Mathlib's
   `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`:
   translating its module quotients to coordinate ideal quotients needs more
   infrastructure than the existing direct chase. Retained the correct proof.
   Removed the broad `Matrix.ToLin` import and redundant explicit `Matrix.Defs`
   import, replacing them with direct statement imports `Data.Matrix.Mul` and
   `RingTheory.Ideal.Quotient.Basic`. All five old `proof_deps` are covered in
   `No longer needed`; statement dependencies remain. Read
   `dag/units/sk-thm-p1.json`: this node realizes no statement or step there, so
   the node-level change bypasses no unit route.
5. **Nodes and Lean: PASS.** The existing node changes only `proof`,
   `proof_deps` and `proof_origin`; its statement and Lean record are unchanged.
   Its three elementary steps match the proved helper, endpoint injectivity,
   and interior exactness. Their `uses` union and `proof_deps` are both empty;
   no other project theorem is applied. The coordinate presentation of the
   source's argument is explicitly recorded in `proof_origin`.

Second-reading changes: narrowed the imports and corrected the corresponding
report claims. No proof, theorem signature, definition, or node needed repair.
Closed one original hole; added zero holes. No split-off statements remain.


The first second-reader dry run requested a change record for removing public
imports. Added `coord/changes/free_complex_mod_nonzerodivisor_exact-imports.md`,
checked the direct downstream/user list, and compiled the unchanged sole direct
importer `Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors` against the narrowed
module in an isolated scratch sandbox. Both compile cleanly. Its import of this
module is private, so the import change does not propagate to its public users.
No adapted module is delivered.
