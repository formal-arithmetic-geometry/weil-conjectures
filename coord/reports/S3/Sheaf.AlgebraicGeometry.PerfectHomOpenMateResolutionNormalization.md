## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectHomOpenMateResolutionNormalization.lean`
from its rework quarantine as a public compatibility import of
`WeilConjectures.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization`.
The adopted source already supplies `perfectHomOpenDerivedComparison`,
`perfectHomOpenSuppliedComparison`, and the complete proof of
`perfectHomOpenComparison_counit_resolution`.

Retained the node's exact statement, all three declaration names, all statement
and proof dependencies, and its categorical proof plan. The Lean attachment now
points to the existing adopted source module. The quarantine archive is preserved;
there is no withdrawal, new module of mathematics, or consumer adaptation.
The change record is
`coord/changes/S3-perfect-hom-open-normalization-restoration.md`.

Searches: local source search found the complete adopted theorem; LeanFinder's
open-restriction query returned the ordinary restriction API, Loogle returned
`mateEquiv_counit` and `iterated_mateEquiv_conjugateEquiv`, and the Mathlib grep
confirmed those same categorical lemmas. Reusing the complete library proof is
the shortest route. Its ordinary mate, exact derived-mate compatibility and
normalized square-unit dependencies are themselves proved in the adopted source.
The Stacks arguments at Tags 08FE, 08BS, 079W and 0D5S were read locally.

The compatibility module compiles cleanly in 1.9 seconds. A separate compiled
axiom probe (1.8 seconds) reports exactly `propext`, `Classical.choice` and
`Quot.sound` for both comparison constructions and the normalization theorem.
A compatibility file compiles in 9.5 seconds: it reconstructs both archived
comparison definitions (using the current additive witness), proves their equality
to the adopted definitions by `rfl`, and checks the complete archived theorem
signature by applying `perfectHomOpenComparison_counit_resolution`. Its axiom
prints again show only the same three permitted axioms.
The actual restored wrapper (1.9 seconds) and a scratch copy of the direct
consumer `PerfectHomOpenComparisonMateIso` (5.6 seconds) compile together in
import order, with its import changed to the restored Sheaf path. This checks the
parent's complete proof through the re-exported interface. The scratch checks
are outside the delivered Lean tree.

## Proved and sorry left

This is an assigned zero-hole rework repair. The archived module has zero
`sorry`s; the restored compatibility module has zero. Holes closed: none.
Holes added or split off: none. No declaration remains with `sorry` in the delivery.

The existing adopted proof of
`AlgebraicGeometry.perfectHomOpenComparison_counit_resolution`
(node `lem-pc-perfect-hom-open-mate-resolution-normalization`) is reused.
The explicit comparisons `AlgebraicGeometry.perfectHomOpenDerivedComparison` and
`AlgebraicGeometry.perfectHomOpenSuppliedComparison` are re-exported under their
existing names.

## No longer needed

The restored Sheaf file replaces its eight archived direct imports with one
public import of the complete adopted normalization module. The old imports are:

- `WeilConjectures.AlgebraicGeometry.PerfectHomOpenModuleMate`;
- `Sheaf.AlgebraicGeometry.PerfectHomTransport`;
- `WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData`;
- `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`;
- `Sheaf.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties`;
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate`;
- `WeilConjectures.CategoryTheory.DerivedExactMateCompatibility`;
- `WeilConjectures.AlgebraicGeometry.NormalizedDirectImageSquareUnit`.

The two retired Sheaf dependencies are supplied by their adopted source modules;
the affine-map compatibility import is supplied directly by its source module.
All mathematical dependencies remain used through the adopted proof. No DAG node
or additional library module is pruned from the targets' import closure. The
three archived private categorical helpers and local proof instances need no
second copies at the restored path; the adopted proof keeps their counterparts.

## Where the brief, the DAG or earlier work was wrong

The current rework row, rather than an old return or absence from lean/, identifies
the archived item. It is a zero-hole build restoration, not a new missing proof.
The first archive restoration with only the open-immersion import/helper repair
failed with `Unknown identifier perfectHomComposition`: its Sheaf transport
import is now withdrawn. The adopted proof also uses the current comparison lemma
`rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived` and an explicit
small-colimit instance, avoiding the archive's obsolete elaboration choices.

The earlier retirement census marked the upstream comparison definition
DIFFERENT. The source and archive show the same explicit construction, with the
additive-instance witness synthesized from the current source API. The packet
checks equality of the actual constructions rather than assuming an arbitrary
isomorphism has the required normalization. The dependency on the normalization
node and the unit route are retained; zero current importers are not used to
justify dropping any mathematics. No source-library declaration is changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
