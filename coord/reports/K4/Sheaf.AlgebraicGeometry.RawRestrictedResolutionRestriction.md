## What changed

Proved `AlgebraicGeometry.Etale.rawRestrictedResolution_restriction` with its exact
original statement. The proof checks the augmentation square, applies the existing
K-injective pullback abutment theorem, identifies section restriction using
object-sections naturality, and applies homology naturality under evaluation.
Composition and cancellation prove the equality for any prescribed resolution,
then for `injectiveResolution F`. All private helpers are proved.

`RawRestrictedClassNormalizationData` names the original complex and augmentation,
and shares the original first comparison factor and coefficient composite. The
original quasi-isomorphism and K-injectivity proofs are retained.
Generic opposite-category glue retains the
original class component, kappa and sheafification lift. All 23 original written
public signatures and public imports are retained. The change record is
`coord/changes/raw-restricted-resolution-sharing.md`; its data declarations are
attached to the existing normalization-data node. No source-library file changes.

Proof imports are `EtaleInjectiveSectionsComparison`,
`EtaleKInjectivePullbackAbutment`, `EtaleKInjectiveUnitLeray` and
`ObjectSectionsNaturality`. The `import all` exposes the proved private
sections-unit identity used in the section comparison. The original public data
import remains. The proof is uniform in q=0, zero coefficients and empty charts.

The final changed modules compile: data 38.8 s and restriction 40.6 s. A separate
semantic audit compiles in 28.4 s. Its five `rfl` checks compare the base complex,
base augmentation, restricted augmentation, full normalization isomorphism and
cohomology restriction with their original expressions. `#print axioms
AlgebraicGeometry.Etale.rawRestrictedResolution_restriction` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

All twelve actual consumers identified by the scan were checked. Eight passed
the per-file limit. Four completed kernel checking without Lean errors but
exceeded the limit; each also exceeds it in an isolated copy against the
unmodified published library:

| Consumer | Packet check | Published baseline |
|---|---:|---:|
| RawRestrictedClassNormalization | 67 s | 66 s |
| ResolutionSectionCocycleSheafification | 80 s | 80 s |
| PrimeCurveArtinSchreierKernel | 71 s | 66 s |
| RawRestrictedResolutionNaturality (new shared proof) | 80 s | 71 s |

These existing timing failures are reported for maintenance; no consumer
signature, definition or proof is changed in this packet. The other consumers
passed: CoherentHigherImageModuleAction, RawRestrictedResolutionClass,
RawRestrictedResolutionCocycle, ResolutionCocycleAdjunctionClass,
UnitCoherentRawEvaluationFormula, UnitScalarRawData, UnitScalarRawEvaluation and
SheafHDerivedPullback. Temporary audits and baseline copies are not delivered.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.rawRestrictedResolution_restriction`:
1 of 1 proved, zero split off, zero new holes. No `sorry` remains in the item or
the changed data module (actual hole count: zero). No axiom or hollow definition
was introduced.

## No longer needed

No original import was removed. The proof no longer directly uses the planned
nodes `lem-weil-pbc-sections-comparison-triangle-naturality`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-sbc-etale-abelian-restriction-injectives`, and
`lem-weil-pbc-etale-restriction-pullback-unit-eq`. Their roles are handled by the
existing abutment theorem, restricted-resolution data and object-sections
naturality. `lem-weil-pbc-inverse-image-composition` remains needed. The generic
single-complex proofs need no direct `EtalePullbackSingleComp` import.
These omitted direct dependencies may still be needed transitively or by other
consumers. No module or adopted declaration is withdrawn; modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The statement is retained. The proof plan can reuse the proved K-injective and
object-sections comparisons instead of repeating their derived-unit and terminal-
section calculations. Some node attachments name Sheaf wrappers; the proof uses
the existing proved implementations in the corresponding WeilConjectures modules.
Sharing names for the original constructions and using generic categorical glue avoids
repeated conversion of the large concrete sheaf-category structures.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
