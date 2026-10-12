## What changed

Replaced the sorry in `AlgebraicGeometry.ml_cohomology_powers_ideal` by a reduction
from two strictly smaller statements, in new modules:
- `Sheaf.Paper.MLCohomologyPowersIdealKernelBound` states only the kernel bound.
- `Sheaf.Paper.MLCohomologyPowersIdealImageStabilization` states only image stabilization.

The original module combines their independent constants by taking their maximum,
using decreasing ideal powers and monotonicity of submodule scalar multiplication.
It proves Mittag-Leffler directly from image stabilization, using Mathlib's
`Functor.isMittagLeffler_iff_subset_range_comp`; index `op j` means quotient level `j+1`.
Existing signatures and all public imports are unchanged. New imports into the original
module are plain proof imports. The three old proof-only imports are moved to the two
split modules, whose unfinished diagram chases use their declarations.

## Proved and sorry left

Closed upper hole: `AlgebraicGeometry.ml_cohomology_powers_ideal`.
Added holes:
- `AlgebraicGeometry.ml_cohomology_powers_ideal_kernel_bound`, node
  `ml-cohomology-powers-ideal-kernel-bound`.
- `AlgebraicGeometry.ml_cohomology_powers_ideal_image_stabilization`, node
  `ml-cohomology-powers-ideal-image-stabilization`.

Both are whole proofs of public named theorems with complete proof docstrings and sources.
This is a decomposition: one old hole closed, two lower holes added, net -1 in the
item's import closure. No original theorem is proved without sorryAx (0 of 1).
The common-constant argument and the Mittag-Leffler consequence are now checked proofs.
The first worker's bounds and Mittag-Leffler holes and their nodes were removed, not landed.

## No longer needed

No module is pruned from the targets' import closure. The original theorem's old direct
proof dependencies are now routed through the split statements:
`def-weil-pbc-coherent-formal-module`, `pqf-def-cohomology`,
`lem-weil-pbc-cohomology-powers-ideal-application`,
`lem-weil-pbc-scheme-modules-enough-injectives`, and
`lem-weil-pbc-horseshoe-delta-functor`.
The last three corresponding proof imports were removed from the original module and
retained in each split module. The first two statement imports stay in the original module.
No mathematical ingredient of either diagram chase has been pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes depended on their parent, making a circular proof plan.
They lacked stmt_deps, Lean signature records, Mathlib searches and complete proof docstrings.
Their report described conjunction assembly as a proof and treated Mittag-Leffler as an
independent substantial component, although it follows directly from stabilization.
The combined bounds statement was too close to the full item. It is replaced by the
separate kernel and image statements, and the original module now contains a real reduction.
No statement dispute or interface change is required.

## New nodes

`ml-cohomology-powers-ideal-kernel-bound` isolates Stacks 02OB(1). Its proof plan uses the
long exact sequence and 02OA's image estimate in degree p; no parent dependency remains.
Its complete statement, source, natural-language proof and Lean signature are recorded.

`ml-cohomology-powers-ideal-image-stabilization` isolates Stacks 02OB(3). Its proof plan
uses the natural ladder and 02OA's kernel equality in degree p+1, followed by exactness.
Its complete statement, source, natural-language proof and Lean signature are recorded.

Three kinds of Mathlib search were run through msearch.py. Leansearch was unavailable
(Internal Server Error), recorded without a mathematical verdict. Leanfinder found local
cohomology and module completion facts, not these scheme-module statements; grep found
no reduction bounds. The Mathlib range criterion supplies the Mittag-Leffler consequence.
Searches of lean/Sheaf, lean/WeilConjectures and the upstream source found no duplicate.
There are no change records: no existing signature, definition or public import changed.

## Second reading by T1

1. Compared the delivered original module with the repository using diff. Its existing
   theorem signature is byte for byte unchanged, including the conjunction indentation.
   No existing definition or visibility changed; all edits are its proof, plain imports,
   the new modules and the DAG proof metadata. Verdict: pass.
2. Compiled all three modules locally in import order through lcompile.py, without errors
   or warnings. Scanned for forbidden declarations and definition holes: none. The two
   named split theorems are the only direct sorries. Scratch #print axioms checks and
   delivery's all-declaration probe allow only the three standard axioms plus sorryAx.
   The original theorem still depends on sorryAx through its two split statements.
   Verdict: valid decomposition, not a completed axiom-free theorem.
3. Read both split statements and complete docstring proofs. Each is strictly a part
   of the original argument, with no parent dependency or duplicate library theorem.
   Checked I=0 (positive quotients are F), I=A (positive quotients are zero and the
   kernel bound is all H), zero F, p=0, n=1, and c=0. The clauses hold in each case;
   the long-exact-sequence chase treats all degrees and positive levels uniformly.
   No data is selected from a sorry existence theorem. Verdict: pass.
4. Checked the top-down reduction, Mathlib search results and imports. Proved the
   Mittag-Leffler consequence rather than retaining the extra hole. Retained the old
   mathematical dependencies below the split statements and reported every old direct
   dependency above. Inspected dag/units/sk-thm-p1.json realized: neither the item nor
   a dependency pruned by this delivery realizes a unit step; no unit route changes.
   Verdict: pass, no modules pruned.
5. Read the original and new nodes against the Lean statements. The original node's
   proof and proof_deps now follow the maximum-constant and range-criterion reduction;
   new nodes carry statement dependencies, noncircular proof plans, signatures and
   recorded searches. Verdict: pass.

Second reading changed: replaced the two inadequately documented and circular split nodes
by kernel and image components in separate modules; proved common-constant assembly and
Mittag-Leffler; restored the exact original signature; repaired DAG records, imports and
this report's hole accounting.
