## What changed

Retired the zero-hole duplicate
`Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition`, as explicitly
requested in `coord/retire-items.tsv`. Its only declaration already exists in
`WeilConjectures.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition`.
The upstream signature has the same conclusion and omits the unused `hM`
torsion hypothesis. The two direct consumers now import that upstream module,
omit `hM` at its application, and retain `hM` in their unchanged signatures.
Both retain all existing proof steps after the application.

Reattached `lem-sc-generic-finite-primary-decomposition` to the upstream
module and recorded its actual signature. Preserved its mathematical
statement and both proof dependencies. The upstream proof implements the
same equivalence/primary-decomposition/transport argument. The unit
`sk-prop-cd-affine` has no realization entry for this split; its route is
unchanged, and both parent nodes still use the same decomposition node.

Validation: both changed consumers compiled remotely (7.1 s and 7.7 s),
without errors or warnings. Their declaration inventories and signatures are
preserved. All 13 downstream import closures were checked: the withdrawn
module is absent, and the migration introduces no new pair of Sheaf/upstream
twin modules into a common environment.

Change record: `coord/changes/E7-retire-generic-finite-primary-decomposition.md`.

## Proved and sorry left

The item initially had zero `sorry` holes. Closed: none (0 of 0).
Added: none. Split off: none. No `sorry` remains in the delivered consumers.
`AlgebraicGeometry.Scheme.exists_finite_primary_sheaf_decomposition` remains
proved in the unchanged upstream module, with the same finite-primary
summands and projection/inclusion sum identity.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition`.
Removed its proof import from both
`Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData` and
`Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension`.
Each imports the upstream twin instead. Repository search found exactly
these two direct importers and declaration users.

The duplicate's private proof imports
`Sheaf.AlgebraicGeometry.AbelianSheavesGModules`,
`WeilConjectures.RepresentationTheory.FinitePrimaryDecomposition`, and
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` disappear with the
withdrawn implementation. The last two are still used by the upstream proof.
The older Sheaf equivalence is no longer needed by this decomposition's Lean
implementation; it has other consumers and is not withdrawn by this delivery.
No mathematical node is deleted or made unnecessary by retiring the copy.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes, but the current item
is a listed duplicate retirement with zero holes. Its upstream twin differs
only by dropping the unused torsion premise and using the canonical upstream
equivalence. This difference requires removing that argument at both call
sites; an import-only replacement would not typecheck.

The upstream result applies to zero stalks and all characteristics, keeps
the original coefficient universe, and gives exactly the same prime,
finiteness, primary-group, and sum-of-composites clauses. Retaining the
original torsion hypotheses in both consumers preserves their statements.

Searches: `msearch.py` leanfinder returned general etale/primary torsion
results, without an exact sheaf theorem; loogle and grep found no Mathlib
match. Direct `rg` in both library roots found the exact upstream theorem.
The existing source is the shortest route; no new mathematical lemma is
needed. The source blueprint paragraph on separating finite primary parts
and the node's transport proof were read against the two implementations.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
