## What changed

Proved `Matrix.GeneralLinearGroup.complete_nonarchimedean_matrix_group` in
`Sheaf.GroupTheory.CompleteNonarchimedeanMatrixGroup`, preserving its full statement,
universes, public imports and existing docstrings. Added proved private helpers for the
submultiplicative maximum-entry norm, completion inequality, inverse bound, additive
Cauchyness of unit values, convergence of two-sided Cauchy maps, and two-sided completeness.
The auxiliary matrix NormedRing is a real construction using the existing Pi metric;
its multiplicative inequality is proved before the construction.

Added private proof imports of Mathlib's normed-ring units API, ultrametric group and
finite-product APIs, and matrix norm API. Updated the item's proof plan to the actual
Lean proof. No other module or interface changes.

The proof handles arbitrary proper filters, then specializes to the requested directed
nets. Both limits determine a unique unit by ab=ba=1; no arbitrary data is extracted
from an unproved existence theorem. Empty matrices require only N(I)≤1 and are covered
without assuming the index type is nonempty. Trivial norms and B=0 also remain included.

## Proved and sorry left

Closed 1 hole:
`Matrix.GeneralLinearGroup.complete_nonarchimedean_matrix_group`
(node `lem-sfb-complete-nonarchimedean-matrix-group`).
Added 0 holes; 0 remain; 0 statements split off.
All private helpers are completely proved.

The final file compiled cleanly using lcompile.py in 11.3 seconds after import
cleanup. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`
for the theorem. Delivery preflight checks all declarations independently.

## No longer needed

Removed the explicit private import `Mathlib.Analysis.SpecificLimits.Basic`; the
normed-ring geometric-series API supplies the needed convergence theorem.
The proof no longer directly invokes `lem-wf-geometric-decay`: its separate power-decay
and coordinate geometric-sum argument is replaced by Mathlib's proved geometric-series
and units embedding theorems. Removed that direct proof dependency from the node.
The completion and complete-space Cauchy-convergence leaves remain used.
No Sheaf module was withdrawn or pruned, and no source-library declaration was changed.
The unit's realized statements and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original plan is longer than necessary: Mathlib's
complete normed-ring API already proves geometric inverses and the inducing topology.
The ultrametric inverse bound follows directly from the unit equations, without
estimating a second geometric series. General proper filters also avoid a separate
net-to-filter completeness theorem.

The latest blueprint direct-images proof now differs from the older imported unit
text; this delivery does not change either unit or the assigned mathematical statement.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
