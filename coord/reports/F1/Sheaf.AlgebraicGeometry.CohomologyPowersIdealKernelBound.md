## What changed

Proved `AlgebraicGeometry.cohomology_powers_ideal_kernel_bound` with its signature unchanged.
The proof obtains the finite Rees action from the existing Rees-finiteness theorem, proves
transition composition and multiplication compatibility by cancelling image inclusions, and
uses bounded-degree generation of the graded kernel. Both kernel inclusions are proved in Lean.

Added `Sheaf.Algebra.Module.ReesKernelGenerators`, containing the fully proved generic theorem
`ReesAlgebra.bounded_generators`. It constructs the graded submodule, obtains finite generators
by Noetherianity, bounds their supports, and proves the degreewise span claim by span induction.
Updated the item's node to match this proof. The second reader removed the helper's
redundant public import of `Mathlib.RingTheory.Noetherian.Basic` and synchronized its node's
verbatim Lean statement. No existing interface or definition changed.
Both modules compile with no warnings through lcompile.py.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.cohomology_powers_ideal_kernel_bound`
(node `lem-weil-pbc-cohomology-powers-ideal-application-kernel`).
Added a fully proved helper, `ReesAlgebra.bounded_generators`
(node `lem-weil-pbc-rees-kernel-bounded-generators`).
No holes added or left in either delivered module; zero statements split off with sorry.
This closes the item's direct hole using the existing library dependencies; their transitive
axioms include `sorryAx` (explicit second-reader `#print axioms` check), while the helper
uses only `propext`, `Classical.choice`, and `Quot.sound`. This report does not claim the whole
target closed.

## No longer needed

Removed the direct proof import `Mathlib.RingTheory.Noetherian.Basic` from the item because
Noetherianity is used inside the new generic theorem, whose module imports it. No module or node
is pruned from the transitive closure. The old direct proof dependencies
`lem-weil-pbc-noetherian-submodule-finite` and `lem-weil-pbc-rees-algebra-noetherian` move below
`lem-weil-pbc-rees-kernel-bounded-generators`; they are no longer direct dependencies of the item.
The second reader also removed the new helper's redundant public import
`Mathlib.RingTheory.Noetherian.Basic`: `Mathlib.RingTheory.ReesAlgebra` already publicly imports
`FiniteType`, then `Noetherian.Orzech`, then `Noetherian.Basic`.
The stalk theorem itself is not applied; the ideal-product construction and image inclusions in
its module are needed. All existing public imports are retained for the unchanged interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The dry run's interface scanner falsely reports a changed
command: the original signature's `(∀ n : ℕ, c ≤ n →` continuation is unindented, and
`leanindex.commands` includes the proof in an `other` command. No actual command or interface
changes. This tool issue is reported in
`coord/changes/cohomology-powers-ideal-kernel-bound-scanner.md` for the maintainer and reader. The plan did not provide a Lean theorem for the homogeneous-generator
step; the new generic theorem supplies and proves it. The degree-zero target in the multiplication
maps is written `0 + k`, so the proof keeps that expression when composing dependent morphisms.
The unit's statement and realized steps are unchanged. The source was read directly at Stacks tag
02OA because the local literature payload is absent. LeanSearch returned an internal server error;
LeanFinder, Loogle, local Mathlib searches and blueprint search were used as recorded in the node.

## New nodes

`lem-weil-pbc-rees-kernel-bounded-generators`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-rees-kernel-bounded-generators.json`, realizes the
bounded-degree generation and degree projection part of Stacks 02OA. Its theorem is fully proved
and contains no sorry. The empty generating family, zero modules, zero and unit ideals, and
n=0 are covered by the same proof; no cancellation or nonzero hypothesis is used.
Change record: `coord/changes/cohomology-powers-ideal-kernel-bound-scanner.md`, documenting the
preflight scanner's false interface-change finding. No existing signature, definition or
visibility changes.


## Second reading by F1

1. **Unchanged interface — PASS.** Read the full repository and delivered modules and their diff.
   The sole existing theorem signature was also compared programmatically, byte for byte, from
   `theorem` through the conclusion before `:= by`: identical. Its docstring, visibility,
   definitions, and public imports are unchanged. Only its proof and proof-only import change.
   The other module is new and has no existing declarations to change. The scanner issue in the
   change record is real: the unindented conclusion continuation belongs to the original file.
2. **Proof and axioms — PASS with existing upstream holes.** Both files compile without errors
   or warnings through `lcompile.py --all`, including after the import repair. Searched both
   delivery sources for sorry and prohibited declarations/options: none. Explicit scratch-copy
   `#print axioms ReesAlgebra.bounded_generators` reports only `propext`, `Classical.choice`,
   `Quot.sound`; `#print axioms AlgebraicGeometry.cohomology_powers_ideal_kernel_bound` also
   reports `sorryAx` from existing dependencies. There are no delivered definitions and no
   arbitrary data chosen into a definition from an unproved existence theorem. The local
   existential elimination of the existing Rees-finiteness theorem is inside a theorem proof.
3. **New statements — PASS.** No statement is split off with sorry. The fully proved helper is
   strictly the bounded-generation part of the argument, not the kernel estimate under another
   name. Read its convolution closure, finite-generator supports, and span induction in full;
   its final conclusion is exactly what the target proof needs. Traced the empty generating set,
   zero homogeneous component, zero module, zero ideal, unit ideal, and n=0 cases: empty sums
   give zero, degree equalities handle n=0, and no cancellation/nonzero ideal assumption appears.
   Independently searched LeanFinder for finite-range generation of direct-sum submodules,
   Loogle for `"FG", "DirectSum"` (zero hits), the local Mathlib direct-sum/graded-algebra files,
   and both project roots. GradedAlgebra finite-type generators concern algebras, and homogeneous
   submodule declarations supply no shorter generation theorem for this convolution family.
   The similarly named Paper kernel-bound theorem concerns quotient reduction maps and depends
   downstream on this item. No duplicate or usable shorter route found.
4. **Top-down argument and pruning — PASS after reporting repair.** Read the supplied Rees
   finiteness theorem and the original proof plan. The proof starts with that theorem, derives
   transition composition and multiplication compatibility by cancelling the actual image
   inclusions, applies the new proved bounded-generation theorem, and proves both kernel
   inclusions. Checked the bound d<=c0<=c and transition factorization through degree k.
   The helper uses Mathlib Noetherianity and finite generation directly. Removed its redundant
   public Noetherian.Basic import; the two remaining public imports supply its signature and
   instances. Existing public imports preserve the existing module interface. The report now
   names every removed old direct proof dependency explicitly; these dependencies move below
   the helper, and no transitive module is pruned. Read dag/units/sk-thm-p1.json `realized`:
   neither item nor helper replaces a realized unit-level step; this is the same subordinate
   formal-functions route beneath finite-etale lifting.
5. **DAG agreement — PASS after verbatim-record repair.** Compared the existing node diff:
   only proof, proof_deps, and proof_origin change. Checked the union of each node's step uses
   against proof_deps and matched them with the Lean proof and Mathlib leaves. The stalk result
   is not invoked as a theorem; its module supplies the ideal-product image definitions.
   The new node includes its source, complete statement, statement dependencies, proof steps,
   proof origin, searches, split status, creation record, blueprint ancestry, chapter/unit,
   and Lean record. Replaced its whitespace-flattened Lean statement with the verbatim theorem
   signature. Independently read [Stacks Lemma 02OA](https://stacks.math.columbia.edu/tag/02OA),
   especially the graded-kernel argument in the proof of (3); both proofs follow it.

**Second-reader changes:** removed one redundant helper import; synchronized the helper node's
verbatim Lean statement; corrected the report to distinguish the existing hole closed from the
new fully proved helper, name moved dependencies explicitly, and state the transitive sorryAx
limitation. No proof, existing statement, definition, or unit route needed repair.
