## What changed

Restored `Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates`
from its exact quarantine archive. Explicitly fix the module universe in the
local `coefficientCoordinatesAbelian` instance. In the final proof, identify
scheme pushforward with ringed-space module direct image by definitional
reduction, then apply the existing factorization theorem and distribute functors
over composition.
The public theorem signature, docstrings, options, and both imports are unchanged.

Updated only `proof` and `proof_origin` of the existing node
`lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates` to record that
conversion. Its Lean attachment, statement, dependencies, and unit are retained.
Change record: `coord/changes/E4-affine-coefficient-coordinates-rework.md`.

## Proved and sorry left

This is a zero-hole rework assignment. The archive contains zero `sorry` and the
restored module contains zero `sorry`. Holes closed: 0. Holes added: 0. Split off: 0.

`AlgebraicGeometry.affineTildeCoefficientPushforwardHomologyCoordinates` retains
its complete proof from the existing factorization theorem. Its node is
`lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates`. No declaration
is left with a `sorry`. The repaired local instance is also complete.

The repaired module compiled without errors or warnings in 42.3 seconds via
`lcompile.py`. A textual comparison confirms the entire archived public theorem
signature is unchanged, and every Lean line has at most 100 characters.
A separate consumer imports the restored module, restates the exact archived
public type, and proves it by applying the imported theorem. The module and
consumer compile in 41.1 and 14.1 seconds respectively. Both `#print axioms`
checks return exactly `propext`, `Classical.choice`, and `Quot.sound`.
The delivery dry run passes compilation and server preflight (review class CODEX).

## No longer needed

None. Both original imports are needed: the public normalization import supplies
the statement's constructions, and the private factorization import supplies the
proof. All statement and proof dependencies remain. No module or node is pruned,
and the quarantine archive is preserved untouched.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief mentions an open hole, but the current rework row assigns
restoration of an already-proved module with an instance-synthesis error. The
original archive reproduces the recorded missing locally-bijective instance and
stuck universe constraints. Fixing that instance also exposes the mismatch with
the factorization theorem's new pushforward presentation; explicit definitional
normalization repairs this without changing the theorem's statement.

The adopted source tree has the same named theorem, proved by the same
factorization argument. It imports the source normalization module, which defines
the same named comparison declarations as the Sheaf normalization module used by
this item's archived consumer. Importing both normalization modules would create
duplicate constants. This delivery keeps the assigned Sheaf interface and its
existing dependency route instead of introducing that import collision. No
source-library file is changed.

Short-route searches: LeanFinder returned eight sheaf-pushforward infrastructure
hits, with no more specific replacement. Loogle `CategoryTheory.Functor.map_comp`
found the existing composition law used by the proof. The msearch grep endpoint
returned no hits; direct `rg` on both library roots found the source counterpart
and the already-proved factorization. The node route needs no additional theory.
No mathematical statement or unit route is disputed or changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
