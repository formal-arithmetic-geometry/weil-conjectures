## What changed

Restored `lean/Sheaf/Paper/CondensedPointDiscreteConstantComparison.lean` byte for byte
from its authoritative quarantine archive, as assigned by `coord/rework.tsv`.
The live source was absent after a reverted cluster restore. This restores the complete
proof of `AlgebraicGeometry.ProEtale.condensed_point_discrete_constant_comparisons`,
including its private locally bijective constant-function comparison and internal-ring
sheafification helpers. All declaration signatures, definitions, imports and attributes
are preserved. The existing node attachment and dependencies remain unchanged.

The restored item compiles with `lcompile.py` in 7.1 seconds. A separate importing axiom
probe compiles in 2.2 seconds and reports only `propext`, `Classical.choice`, and
`Quot.sound`. The unchanged archived direct consumer
`Sheaf.Paper.CondensedPointCoefficients` compiles against the restored sandbox module in
5.9 seconds; that consumer was checked in the scratchpad and is not part of the delivery.

The recovery change record is
`coord/changes/A7-restore-condensed-point-discrete-constant-comparison.md`.

## Proved and sorry left

The archived item already had zero holes. Zero existing holes closed, zero holes added,
zero split off, and zero sorries left in the delivered module.
`AlgebraicGeometry.ProEtale.condensed_point_discrete_constant_comparisons` is fully proved
(node `lem-pe-condensed-point-discrete-constant-comparisons`). All private theorems and
instances in the module are proved as well. This is source recovery, not a newly closed
proof obligation or a decomposition.

## No longer needed

None. No imports, declarations, nodes or modules are pruned. The proof uses the canonical
monoidal constant-sheaf pullback comparisons and all recorded dependencies are retained.
Fresh LeanFinder, Loogle and grep searches found generic discrete/locally constant sheaf
interfaces, but no replacement for the complete internal-ring comparison for arbitrary
rings. The archived proof already follows the shorter locally bijective sheafification
route recorded by its node.

## Where the brief, the DAG or earlier work was wrong

The assigned live file is missing, but its quarantined archive contains a complete,
currently compiling proof. It must be restored, rather than withdrawn or replaced by a
new split. No new mathematical error was found. The node and source agree with the two
constant-ring conclusions; the unit's coefficient assertion and route are retained.

The proof explicitly handles empty profinite spaces by the empty covering. It requires
neither commutativity nor a nonzero coefficient ring, and the finite-image covering
argument works for infinite discrete rings as well. No target statement or definition
meaning changes, and no consumer adaptation is needed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
