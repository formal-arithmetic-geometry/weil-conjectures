## What changed

Repaired the stale-base return by comparing the retained packet with the current
source and reapplying the proof change to the current source file. The current
source already has a complete proof and all four private helpers. They are
preserved, together with every existing signature, attribute, public import,
definition and docstring.

Refactored the proof of
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`:
first compose smooth lisse Verdier duality with the sheaf-level Tate-tensor
comparison, then apply derived direct image and its shift comparison. Apply
homology in degree `-i`, use `i + j = 2*d`, and compose with the existing private
point-duality equivalence. Transporting evaluation along that equivalence gives
the perfect Frobenius-invariant pairing. All four existing private helpers remain
fully proved and unchanged.

Removed the unused private proof import
`WeilConjectures.WeilSheaf.ConstantTwistCohomology`: the twist comparison takes
place before cohomology. This is a proof refactor and dependency pruning on the
current source, rather than an unchanged resubmission of the rejected packet.
No additional module or public API is changed.

## Proved and sorry left

The item has zero proof holes on the current source and zero after this repair.
Closed 0 of 0 current holes; added 0 holes; split off 0 statements.
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
retains a complete proof. No sorry remains in any declaration in the item.

The earlier packet reported closing this theorem's one original hole. That count
belongs to its old base and is not claimed again here. The proof still uses
existing library theorems with unfinished dependencies, including Verdier
exchange, the left-adjoint instance and compatibility of Verdier duality with
shifts. This packet does not claim to prove those dependencies.

## No longer needed

Removed private import `WeilConjectures.WeilSheaf.ConstantTwistCohomology`.
The argument uses the existing Tate-tensor comparison at the sheaf level instead.
No declarations, nodes or modules are withdrawn; this removes one direct proof
import, not a claim of pruning the module from the entire target closure.

## Where the brief, the DAG or earlier work was wrong

The return concerns overlapping source changes since base `ca0fba8ab`. The current
source already contains the complete theorem and the four helpers, so treating
this repair as closing a new hole would double-count progress. The retained proof
refactor has been reapplied to that current source, and the stale report corrected.

There is no DAG node whose Lean attachment names the assigned module or theorem.
The theorem docstring cites `thm-pod-degreewise-perfectness-over-a-field` and
`thm-pod-equivariance-of-the-twisted-pairing`; those are more general statements.
This proof refactor preserves the derived-duality, point cohomology-duality and
Frobenius-equivariance route; no node statement or unit route changes.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
