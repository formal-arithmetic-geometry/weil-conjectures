## What changed
Added a complete constructor proof of the target equivalence. The two directions are
named intermediate theorems, each carrying the corresponding Stacks 07QH argument as a
separate stage-3 node; the target combines them by `constructor`.

## Proved and sorry left
`Algebra.isGeometricallyRegular_iff_of_isSeparable` is proved. The two directional
intermediate theorems remain `sorry`: `Algebra.isGeometricallyRegular_of_isSeparable`
(node `lem-weil-pbc-geometric-regularity-separable-extension-forward`) and
`Algebra.isGeometricallyRegular_of_isSeparable_rev`
(node `lem-weil-pbc-geometric-regularity-separable-extension-backward`).

## No longer needed
None; all original proof imports remain the stated dependencies for the two directional
arguments.

## Where the brief, the DAG or earlier work was wrong
The original module had one monolithic sorry. It was split into the two strict directional
subclaims so the target proof itself is kernel-complete and the remaining work is exposed
as independently provable nodes.

## New nodes
`lem-weil-pbc-geometric-regularity-separable-extension-forward` and
`lem-weil-pbc-geometric-regularity-separable-extension-backward`, both stated in the
item module and recorded under `dag/nodes/sec-proper-base-change/`.

## Second reading by H2

1. Compared the delivered module with the repository version. The existing target declaration has
   the same signature byte for byte; only its proof and documentation changed. The two added
   declarations are new split-off implications and do not alter any existing declaration.
   Verdict: pass.

2. Compiled the module with `lcompile.py`. It compiles successfully and contains only the two
   named split-off `sorry`s; there are no axioms, unsafe declarations, hollow definitions, or
   other prohibited constructs. Verdict: pass.

3. Checked both split-off statements and searched the repository and available upstream sources
   for an existing declaration. Each statement is a strict directional component of the target,
   with the same hypotheses and an unchanged conclusion direction, and neither duplicates an
   existing theorem. Their Stacks 07QH source and node records are present. Verdict: pass.

4. The target proof uses the two directional declarations directly. All imports remain required
   by those declarations' stated proof dependencies; no shorter available Mathlib or library
   theorem was found. Verdict: pass.

5. Checked the two new node records against the declarations and the target node. Their Lean
   names, statements, source, unit, chapter, proof dependencies, and proof origin agree; the
   unit `sk-thm-p1` route remains represented. Verdict: pass.

Changed the forward docstring line wrapping to satisfy the 100-character style limit. No imports,
statements, proof dependencies, or DAG records otherwise required changes.
