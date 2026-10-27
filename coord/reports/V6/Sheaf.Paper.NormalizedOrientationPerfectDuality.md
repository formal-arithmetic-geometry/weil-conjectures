## What changed

Restored Sheaf.Paper.NormalizedOrientationPerfectDuality from its quarantine archive.
Profiling located the original stall at SfPackageIntegralTraceReduction. That
predicate and SfPackageIntegralCounitReduction now use the existing canonical
PurCompactSupport.finiteReductionIso inversely at Y and forwards at X inside
compact support. This identifies the pbcDerivedExtend quotient coordinates with
scalarReductionDerivedExtension by the recorded tensor-unit normalized adjunction
comparison. It preserves the specified finite purity maps, counits and traces.

The integral trace constructions have explicit result types; their composite
bodies are unchanged, and sfPackageIntegralCounitTrace is irreducible. Local
irreducibility protects the chosen derived constructions during elaboration.
The rational, field and common predicates bind the original maps once, specify
their native category presentations, and avoid repeated category synthesis at
projections and compositions. The common finite-stage purity construction reduces
only its field-model wrappers. Its trace uses the proved commonCategory_eq before
the existing inclusion functor. Eight complete generic helpers implement the
ordinary projections, explicit-category composition and this equality transport.

All 17 original declarations remain. The main theorem text is verbatim the archive.
The existing node retains its statement, proof dependencies, parent attachment and
unit route; its Lean declarations and note record the complete helpers and repair.
The changed definitions require independent statement review. Change record:
coord/changes/V6-normalized-orientation-trace-elaboration.md.

Validation: the complete file compiled without errors or warnings in 36.9 seconds,
under the unchanged 60-second limit. Both transparency-respecting options are true;
no heartbeat or time limit is raised. Profiler and marker commands are removed.
Static checks confirm the original theorem text, all original declarations, one
original hole, matching node declarations and lines of at most 100 characters.
The delivery tool will verify the final formatting and packet before pushing.

## Proved and sorry left

This is the assigned timeout/definition repair. Zero holes are closed and zero
split-off holes are added. The sole original hole remains:
WeilConjectures.sfPackageNormalizedOrientationPerfectDuality
(lem-sf-package-normalized-orientation-perfect-duality), with its original statement
and complete proof in words. No sorry occurs inside a definition.

The new complete constructions are WeilConjectures.sfPackageFunctorObject,
WeilConjectures.sfPackageFunctorMap, WeilConjectures.sfPackageIsoHom,
WeilConjectures.sfPackageIsoInv, WeilConjectures.sfPackageNatTransApp,
WeilConjectures.sfPackageIsoApp, WeilConjectures.sfPackageCompose and
WeilConjectures.sfPackageTransportHomCategory. Each is an ordinary projection,
composition or equality substitution, with no choice or remaining proof obligation.
They belong to the same item node; no new theorem or node is introduced.

## No longer needed

Removed the unused direct proof import Sheaf.Paper.SitePerfectCoefficientDual.
Its theorem is not applied by this file and is not a stated dependency of this
node. No DAG node, module, proof dependency or unit step is withdrawn. The DAG
parent prop-functor-package still needs the restored item. Downstream --uses scans
for the eight changed original definitions and a separate lean/ and quarantine/
consumer search find no Lean importer or consumer requiring adaptation.

## Where the brief, the DAG or earlier work was wrong

The archived reduction predicates composed pbcDerivedExtend-coordinate comparisons
directly with scalarReductionDerivedExtension-coordinate maps. The canonical
bridge already exists in the support-comparison library. Unfolding independently
chosen derived tensors to force their equality stalled elaboration. Both ends of
both squares now use that bridge. The later rational/field/common equations also
repeated expensive category inference; ordinary implicit projection wrappers and
explicit native-category composition preserve those equations while avoiding it.

The local diagnostic wrapper allows 120 seconds, while the brief describes a
300-second diagnostic limit. The 60-second acceptance limit is preserved.
The quarantine archive is restored, not deleted or withdrawn. No other group or
source-library module is changed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
