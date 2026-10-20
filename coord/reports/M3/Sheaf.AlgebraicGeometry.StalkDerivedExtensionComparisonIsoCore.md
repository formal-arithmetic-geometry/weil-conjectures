## What changed

Restored lean/Sheaf/AlgebraicGeometry/StalkDerivedExtensionComparisonIsoCore.lean
from its coord/rework.tsv quarantine path. Added public import
Sheaf.Algebra.Homology.KFlat, which defines IsAcyclicTensorKFlat used in the
existing public theorem signature. All archived declarations, signatures and
proofs are retained verbatim. The remote single-file compiler accepted the
restored file in 42.7 seconds with no warnings or errors.

The interface repair is recorded in
coord/changes/M3-stalk-comparison-kflat-public-import.md. Read the archived direct
consumer StalkDerivedExtensionComparisonIso: it applies the unchanged theorem,
so no consumer adaptation is needed. The existing node attachment, proof steps,
dependencies and unit route remain accurate and are preserved.

## Proved and sorry left

This is the assigned compilation repair, with zero original holes. The complete
proof of AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonTransformation
is restored and compiles. Holes closed: none (0 of 0). Holes added: none.
Sorries remaining in the delivered module: none. No split-off statements.

## No longer needed

None. No imports, nodes, modules or declarations are removed. The proof still
uses the tensor-stalk naturality calculation, K-flat derivability, the exact
stalk factors and the universal left-derived lift recorded in the node.
The adopted upstream twin has a different K-flat predicate in its signature;
this repair preserves the assigned theorem and its dependency route.

## Where the brief, the DAG or earlier work was wrong

The rework diagnosis is accurate: the public signature refers to
IsAcyclicTensorKFlat, but the defining module was only a private transitive
proof dependency. The needed repair is an explicit public import, not a new
proof obligation or a statement change. The archived module has zero sorry.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
