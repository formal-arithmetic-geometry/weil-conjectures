## What changed

Filled `WeilConjectures.ConstantScalarUnitQuasiIsomorphism.regular_scalar_unit_quasi_isomorphism`
without changing its signature, its definitions, or its public imports. All auxiliary results
are proved private helpers in the same module.

The proof uses the strict-unit multiplication and reduction-unit formulas, identifies the
ordinary limit by evaluation and reflection of limits, proves epimorphy of the Roos boundary
from the existing pro-etale surjective-tower theorem, and compares the normalized map with the
kernel-to-cocone quasi-isomorphism using both graded projections. Exact countable products
and the existing general derived-product theorem give the specified product cone. Transport
of the mapping-cocone triangle gives the specified distinguished triangle and inverse
projection formula. For completeness the identity K-flat resolution, its canonical quotient
units, and the short exact kernel sequence give the canonical augmented Roos triangle.

Updated the node's proof, proof dependencies and proof origin to record these actual APIs.
No new statements, source-library changes, definition repairs or forced adaptations.
Preflight classifies the added proof elaboration commands as an interface change; their
scope and zero downstream consumers are documented in
`coord/changes/constant-scalar-unit-proof-elaboration.md`. All public definitions and
signatures remain verbatim.
The full module compiled through lcompile.py in 37.4 seconds; the final cleanup removes
its two whitespace-linter warnings. The delivery tool performs the final compile/preflight.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ConstantScalarUnitQuasiIsomorphism.regular_scalar_unit_quasi_isomorphism`
(node `lem-weil-constant-scalar-unit-quasi-isomorphism`).

Holes closed: 1. Holes added: 0. Holes left in the delivered Lean module: 0.
No split-off statements. The proof uses existing declarations, including the strict-unit
statement whose proof is a separate project item; it does not claim those dependencies have
been proved here.

## No longer needed

Removed these redundant proof imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`: the existing finite-coefficient theorem
  already supplies the arithmetic conclusion.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`: no local compactness argument is needed.
- `Mathlib.CategoryTheory.Sites.PreservesSheafification` and
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`: Mathlib's local
  surjectivity/sheafification equivalence gives the needed local lifts directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`: already publicly supplied by the
  surjective-tower dependency.

The direct proof no longer calls `lem-weil-valued-dvr-finite-quotients`,
`lem-pe-ring-sheafification-underlying-sets`,
`lem-weil-pbc-site-sheafification-sections-local`, or
`lem-weil-pbc-module-sheaves-limits-sectionwise`. Mathlib's quotient finiteness,
sheafification and limit-reflection APIs replace these direct steps. Some remain transitive
inputs to retained dependencies, so no global pruning or module withdrawal is claimed.
Removed the obsolete direct `tool_uses` entries for those four nodes, retaining the DVR
and kernel-cocone entries in their original order. No adopted source declaration is removed
or changed. The blueprint unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned explicit local-section and
module-limit constructions have shorter existing Mathlib interfaces. The same ordinary-limit,
epimorphic-boundary and kernel-to-cocone argument applies with independent datum, scheme and
coefficient universes. The unrestricted completeness predicate requires a universe-zero
auxiliary finite-field datum; a prime greater than l supplies it without restricting Y.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
