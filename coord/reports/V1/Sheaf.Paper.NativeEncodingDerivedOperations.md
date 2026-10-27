## What changed

Filled the two remaining theorem holes in
`Sheaf.Paper.NativeEncodingDerivedOperations`. `native_constant_action` is the native
`AdicSheaf.algebraMap_sectionAct` specialized to the unit-applied scalar.
`derivedPushComparison_unit` specializes a proved private generic square calculation:
the four canonical factors of the existing comparison transport their universal units.
Eight proved private helpers make the quotient identities and these equations explicit.
All existing signatures, definitions, attributes and public imports are preserved.
Added only the private proof import of native `Adic.SectionAction`.
Updated the item's node proof, dependencies and proof origin to this argument.
The final module compiled through `lcompile.py` without warnings in 24.6 seconds.

## Proved and sorry left

Closed 2 of 2 original holes, both in node
`lem-sf-native-encoding-derived-operations`:

- `AlgebraicGeometry.ProEtale.NativeEncoding.derivedPushComparison_unit`.
- `AlgebraicGeometry.ProEtale.NativeEncoding.native_constant_action`.

No holes added or split off; no `sorry` remains in the delivered Lean module.
The already proved `weil_resolution_comparison` and
`native_encoding_derived_operations` are retained.

## No longer needed

Removed these unused private imports:

- `Sheaf.Paper.FiniteSpanModuleDerivedComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Paper.CartesianCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.CategoryTheory.FixedPairDerivedForgetComparison`.
- `Sheaf.CategoryTheory.KInjectiveExactSquareComparison`.

The item's direct proof no longer uses these planned dependencies:
`def-weil-pbc-proetale-site`, `lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-equivalence-injective-resolutions`,
`lem-sf-finite-span-module-derived-comparison`, and
`lem-weil-pbc-kinjective-exact-square-comparison`.
Their existing declarations and all statement dependencies are preserved. The core and
source library already supply the required category instances. The normalization follows
directly from the universal unit equations of the canonical composite, so it needs no
additional normalized-square existence theorem. The fixed-pair comparison itself remains
needed and is obtained from the source library through the existing public imports.
Removed obsolete tool approvals for the ring-sheaf, equivalence, finite-span,
K-injective exact-square and cartesian-coefficient nodes from this node's `tool_uses`.
No library module is withdrawn; dependencies may remain needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The remaining unit equation is stronger than
its docstring's resolution argument suggests: the universal equations prove it on all
complexes. Its original K-injective hypothesis is kept verbatim.
The current blueprint places this unit under `sec-six-functors-basics`; the DAG retains
its older `sec-six-functors` directory. This delivery does not change the unit or its route.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
