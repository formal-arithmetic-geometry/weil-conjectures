## What changed

Kept the signature and original mathematical docstring of
`AdicCompletion.local_tensor_quotient_detection` byte for byte. Kept the first
worker's valid n = 0 quotient-zero proof. Replaced the positive-degree restatement
with a genuine reduction: obtain one uniform exponent c >= 1, choose k = n*c,
raise each ideal containment to the nth power, convert quotient vanishing to
membership in the quotient ideal, and apply detection modulo the extended base
ideal power. No definition or existing statement changed. Public-import pruning is recorded in
`coord/changes/local_tensor_quotient_detection_imports.md`, as required by preflight.

The two supporting statements are in new modules
`Sheaf.RingTheory.LocalTensorQuotientPowerBound` and
`Sheaf.RingTheory.LocalTensorQuotientBaseIdealDetection`. They are imported privately
with plain `import`, since only the proof needs them. Removed the unused
`Mathlib.RingTheory.AdicCompletion.Algebra` import and replaced
`Mathlib.RingTheory.TensorProduct.Maps` by the sufficient statement import
`Mathlib.RingTheory.TensorProduct.Basic`. Other retained imports provide localization,
Noetherianity, and module finiteness in the unchanged signature.

## Proved and sorry left

Hole closed: `AdicCompletion.local_tensor_quotient_detection`
(node `lem-weil-pbc-local-tensor-quotient-detection`), by a compiled reduction.
The n = 0 branch is proved without a supporting sorry.

Holes added and left, each exactly `:= by sorry` in its own new module:

- `AdicCompletion.local_tensor_quotient_power_bound`
  (node `lem-weil-pbc-local-tensor-quotient-power-bound`). This gives only one
  uniform first-power containment; it has no tensor sums or quotient detection.
- `AdicCompletion.local_tensor_quotient_base_ideal_detection`
  (node `lem-weil-pbc-local-tensor-quotient-base-ideal-detection`). This gives only
  detection modulo the extended base ideal; it has no exponent choice or local
  maximal-ideal power comparison.

This is a decomposition, not a completed proof: one old hole closed, two new holes
added, net -1 before any wider import-closure ledger measurement. Zero of the one
original declarations is yet free of `sorryAx`. No extra hole is left in the main
module, and no definition or arbitrary witness construction was added. The first
worker's duplicated `local_tensor_quotient_detection_of_pos` and its node/module were
removed from the delivery, not counted as closed baseline holes.

All three files compile locally through lcompile.py. Scratch copies appended
`#print axioms` for every delivered declaration: each uses only `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx`.

## No longer needed

Removed direct import `Mathlib.RingTheory.AdicCompletion.Algebra`; replaced direct
import `Mathlib.RingTheory.TensorProduct.Maps` with
`Mathlib.RingTheory.TensorProduct.Basic`. Neither is needed by the new proof or its
statement. No library module is claimed pruned from the full targets' closure.

Every old proof dependency is no longer a direct dependency of the main node; the
new supporting nodes collectively retain all of them, so none is globally pruned:
`lem-weil-pbc-artinian-local-unique-prime`,
`lem-weil-pbc-fg-ideal-radical-power`,
`lem-weil-pbc-finite-dim-algebra-artinian`,
`lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`,
`lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-localization-at-prime-of-quotient`,
`lem-weil-pbc-localization-base-change`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-localization-prime-residue-field-iso`,
`lem-weil-pbc-product-of-localizations-at-maximal`,
`lem-weil-pbc-tensor-cancel-base-change`,
`lem-weil-pbc-tensor-quotient-base-change`, and
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`.

Removed from this sandbox's proposed delivery:
`Sheaf.RingTheory.LocalTensorQuotientDetectionPositive` and
`lem-weil-pbc-local-tensor-quotient-detection-positive`. These were not library nodes
or modules and merely duplicated the remaining argument.

## Where the brief, the DAG or earlier work was wrong

The first worker declared the same positive-degree helper twice, once in the main
module and once in an unimported new module. Its docstring did not give a complete
proof, its node statement was not self-contained, and its node's sole dependency
was the main theorem: the proposed reduction would make the DAG circular. Adding
n > 0 to essentially the whole original theorem only removes a trivial case; it
is not the required decomposition into parts of the argument.

The repository node's original literature route remains valid. Its proof metadata
now records the actual reduction, and the new nodes record the quotient-product
and cofinal-power steps separately. The local literature file is absent on this
machine, so the reader checked the official Stacks pages directly:
[07N9](https://stacks.math.columbia.edu/tag/07N9),
[0394](https://stacks.math.columbia.edu/tag/0394),
[00JA](https://stacks.math.columbia.edu/tag/00JA), and
[00CT](https://stacks.math.columbia.edu/tag/00CT).

## New nodes

`lem-weil-pbc-local-tensor-quotient-power-bound`: uniform containment N_q^c <= mS_q
for all primes over p. Its complete docstring proof uses the finite Artinian closed
fibre, the radical-power lemma, and a finite maximum. Its source, proof steps,
precise statement, three search kinds, provenance, and verbatim Lean signature
are recorded in the node for `Sheaf.RingTheory.LocalTensorQuotientPowerBound`.

`lem-weil-pbc-local-tensor-quotient-base-ideal-detection`: detects the tensor class
when each local sum belongs to (m^n)S_q. Its complete docstring proof uses the
Artinian quotient-product decomposition and tensor quotient equivalence. The
same metadata fields are recorded in its node for
`Sheaf.RingTheory.LocalTensorQuotientBaseIdealDetection`.

Change record: `coord/changes/local_tensor_quotient_detection_imports.md` documents
the public-import pruning and all downstream users. No statement or definition changed.

## Second reading by S1

1. Compared the main module against the repository with diff and checked the
   existing theorem signature by exact string equality. Verdict: unchanged.
   No existing definition was changed and no other existing module is delivered.
   Import changes above are deliberate and listed, with a change record. The sole
   direct importer independently receives both removed imports through its other
   dependencies. A scratch compile of that unchanged importer timed out at 60
   seconds without an error diagnostic; it is not counted as passing validation.
2. Compiled all delivered modules and axiom-probe scratch copies with lcompile.py.
   Verdict: no errors or non-sorry warnings; the main theorem has no direct sorry.
   The only two holes are the public named supporting theorems listed above;
   no axiom, unsafe, opaque, implemented_by, extern, hollow definition, or arbitrary
   unproved witness definition is present. All axiom lists contain only the three
   standard axioms and the expected sorryAx.
3. Rejected the positive-degree restatement and replaced it by two strictly partial
   steps. Repeated searches with different words through msearch.py: LeanFinder,
   Loogle, grep, and LeanSearch (unavailable, recorded). Searched lean/Sheaf and the
   upstream Lean tree; no exact supporting statement was found. Mathlib supplies
   component tools, including ideal-power containment, quotient/tensor equivalence,
   and product-localization equivalences, but not the two full specialized steps.
   Verdict: both new statements are true, needed, and self-contained, and each has
   its own full natural-language proof and DAG node. Edge cases checked: for empty
   Q choose c = 1 and the Artinian quotient has no primes, hence is zero; for S = R,
   c = 1 suffices and detection is the identity quotient; for a finite product of
   fields over a field every N_q is zero and the product map detects elements;
   for the dual numbers over a field c = 2 is necessary and sufficient, confirming
   why one cannot replace the bound by c = 1. Empty sums vanish, and n = 0 is the
   compiled direct branch. The base-ideal lemma assumes n > 0 explicitly.
4. The main proof follows the original quotient-product/cofinal-power argument
   from the top down, with explicit ideal-power arithmetic and quotient membership.
   Imports used only by the proof are plain imports; unused imports were pruned.
   The `sk-thm-p1` unit record's realized statement and steps were read and are
   unchanged: this auxiliary node realizes none of them, and the reduction retains
   the same literature route. Every original proof dependency remains beneath the
   supporting steps. Verdict: no unit step bypassed and no unreported DAG pruning.
5. Compared every delivered node with its Lean signature and proof. The main node
   records the zero branch, choice k = n*c, containment, and detection. Its two
   dependencies agree with its two plain imports. New nodes have matching verbatim
   signatures, proof-dependency unions, sources, search records, created fields,
   blueprint ancestry, chapter, and unit. Verdict: coherent, no circular dependency.

Changes made by this reading: removed the duplicated positive-degree restatement
and its node/module, kept the valid zero-degree proof, wrote the genuine two-step
reduction, pruned unused imports, added the two proper supporting nodes/modules,
updated the main node, documented public-import pruning and downstream effects,
and corrected the report to count the result as decomposition.
