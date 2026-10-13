## What changed
The existing signature of `AlgebraicGeometry.finite_structure_unit_lift` is byte-for-byte
unchanged. Its proof now obtains existence from the new proof-only import
`Sheaf.Paper.FiniteStructureUnitLiftExistence` and proves uniqueness sectionwise using
symmetry and both left-unit laws. The `ext` tactic reduces equality of maps from the
rank-one unit module to equality on 1, incorporating module linearity.
The new module leaves only the existence construction open. The original node now
records this reduction; the new node records the supporting-quotient and completion
construction. No definition, existing statement, or existing public import changed.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.finite_structure_unit_lift` (one of one original holes).
Hole added: `AlgebraicGeometry.finite_structure_unit_lift_existence`, node
`lem-weil-pbc-finite-structure-unit-lift-existence`, in
`Sheaf.Paper.FiniteStructureUnitLiftExistence`.
This is a decomposition, not a complete proof of the unit lift: one hole closed and
one hole added, net zero. The uniqueness argument is complete. The existence lemma
asserts existence, not unique existence, and is strictly part of the original argument.
Both delivered modules compile without errors or warnings. Explicit `#print axioms`
checks show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the
remaining open existence theorem/imported statements. There are no hollow definitions
or forbidden declarations.

## No longer needed
No imports or library modules are pruned. The original node no longer directly uses
`lem-weil-pbc-module-support-proper-over-base`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, `pqf-lem-coherent-ft-locnoeth`,
`lem-weil-pbc-affine-pushforward-base-change`, `def-pc-tensor-pullback-composition-iso`,
`prop-weil-pbc-grothendieck-existence`, or `def-pc-module-pullback` as proof dependencies.
These dependencies move to the existence node and remain needed transitively.
The undelivered redundant sandbox module `FiniteStructureUnitLiftExists` was removed;
it was never part of the library and is not counted as pruning.

## Where the brief, the DAG or earlier work was wrong
The first report called the target proved without explaining that its existence part
remains open and the net hole reduction is zero. It also omitted an extra sandbox
module containing an unreported sorry. The copied new node incorrectly recorded the
original unique-existence declaration and retained unrelated prior review metadata;
it was not a faithful record of the new Lean theorem. The original node was not
updated to reflect the new proof. These faults are repaired in this delivery.

## New nodes
`lem-weil-pbc-finite-structure-unit-lift-existence` is the strict existence part of the
original theorem, not a renamed copy of unique existence. Its full hypothesis context
is recorded in the mathematical statement and its verbatim Lean signature in `lean`.
Its source is [Stacks 09ZT](https://stacks.math.columbia.edu/tag/09ZT), expanded using
[088E](https://stacks.math.columbia.edu/tag/088E),
[088F](https://stacks.math.columbia.edu/tag/088F), and 0CYS. The docstring explains
annihilation, factorization through the supporting quotient, transition compatibility,
fullness, the scalar formula, and faithfulness for the left-unit identity. No change
record is needed, since no existing interface changes.

## Second reading by W2
1. PASS. Compared the delivered item with the repository using diff and a byte-for-byte
   signature assertion. The only existing interface addition is a plain proof-only
   import; no hypotheses, conclusions, definitions, or public imports changed.
2. PASS as a decomposition. Compiled both modules and scratch copies with explicit
   axiom printing. Only the four axioms reported above occur. The sole delivered sorry
   is the reported named existence theorem; no axiom, unsafe, opaque, implemented_by,
   extern, or data definition with sorry occurs.
3. PASS. Existence is strictly weaker than unique existence; uniqueness is a genuine
   argument in the item, not an application of a renamed whole statement. The quotient
   construction works when G is zero or X is empty (all maps are zero), for I=0
   (reductions recover X), and for I=top (adic completeness forces the zero base).
   Attempted LeanSearch (service unavailable: Internal Server Error); searched Mathlib
   using leanfinder, loogle, and grep with fresh queries, and searched
   lean/Sheaf and lean/WeilConjectures with rg. The returned `unitHomEquiv`, affine
   quotient lifts, and formally smooth ring lifts do not supply the completion unit
   construction. The existing Grothendieck-existence declaration supplies fullness
   but still requires the quotient construction; no short closure was found.
4. PASS. Kept the correct existing uniqueness proof. All existing imports occur in
   the public signature or supply its notions; the new import is proof-only. Every
   former direct proof dependency is listed above and retained on the existence node.
   The `sk-thm-p1` realized statement and steps are untouched; the supporting-quotient
   and completion route remains below the unit level. No unit step is bypassed.
5. PASS after repair. Updated the original node's proof, proof_deps, and proof_origin.
   Corrected the new node's verbatim Lean signature, self-contained statement, proof
   steps, author, blueprint marker, and fresh search records, and removed copied review
   metadata. Its dependency union agrees with its proof steps.
Changes made by this reader: removed the extra unreported duplicate-sorry module;
corrected decomposition accounting and both DAG records; expanded the new theorem's
proof docstring with the factorization and faithfulness details; repaired its blueprint
marker; wrapped two overlong lines; restored the original signature whitespace.
