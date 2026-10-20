## What changed

Restored Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility from its
quarantine archive. Its public scalar-cohomology import and private tensor-unit
proof import now use the upstream WeilConjectures providers. Its required,
unclaimed dependency ScalarCupPositiveResolutionClassCompatibility uses the same
upstream scalar-cohomology provider. These three import-line changes repair the
recorded duplicate externalCupCoefficients declaration after the upstream sync.
Every declaration, signature, definition, docstring, and proof body is retained.

The two scalar-cohomology providers have matching public declarations and bodies;
their differences are copyright text and local-instance names. No mathematical
statement changes. The preserved earlier caller adaptation is kept in scratchpad
and excluded from this packet: the current cluster brief assigns downstream
repairs separately when no root declaration changes. No downstream module or
WeilConjectures source is delivered.

An untouched scratch copy of the current quarantine source was compiled through
lcompile.py and reproduces the exact duplicate externalCupCoefficients import
error in 0.7 seconds. Both repaired modules compile cleanly against the current
published library through lcompile.py: positive dependency 7.9 seconds, root
29.4 seconds. The provider comparison and a non-import-text comparison confirm
that the repair changes no declarations or proof bodies.

Change record: coord/changes/K2-scalar-cup-resolution-upstream-imports.md.

## Proved and sorry left

Zero-hole quarantine repair: 0 of 0 local holes closed in the assigned item;
0 holes added; 0 split off. Its existing theorem
AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility
(new-sc-scalar-cup-resolution-class-compatibility) retains its complete Lean
proof from the existing dependencies, including both proved degree-zero axes.

The required dependency retains its one existing hole, unchanged:
AlgebraicGeometry.Scheme.Modules.scalarCup_positive_resolution_class_compatibility
(new-sc-scalar-cup-positive-resolution-class-compatibility). No other delivered
declaration contains sorry. The main theorem consequently still depends on
sorryAx through the existing positive-degree comparison; this packet makes no
claim that the full comparison is axiom-free. It repairs the assigned import
collision without another split.

## No longer needed

Replaced Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations by the
upstream provider in the root and its positive-degree dependency. Replaced the
root's proof import Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient by the
upstream provider. The duplicate providers are unnecessary on this import path;
they stay in the library for their other consumers. No whole module or DAG node
is pruned. The unit route, all node attachments and dependencies, and the existing
signed statement_change remain intact. No node copy is needed because the proof
route and signatures are unchanged.

## Where the brief, the DAG or earlier work was wrong

The route note describes the older unsigned statement. The current archive and
node already include the 2026-10-15 Koszul factor and its case proof. Reapplying
that correction would invent a statement change; the actual rework is the
2026-10-20 duplicate-provider failure.

The previous packet also restored ScalarCupModuleCupCompatibility with its own
provider migration. The current cluster instruction makes such downstream
failures separate tasks when no root declaration changes, so that file is retained
only in scratchpad. Live and quarantine searches identify it as the direct caller;
its archive, rework row, and all parent node attachments are preserved. The absent
live root is restored, never treated as withdrawn. The earlier tool failure
occurred after compilation while checking out the delivery worktree; the packet
has been retained and checked against current source.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
