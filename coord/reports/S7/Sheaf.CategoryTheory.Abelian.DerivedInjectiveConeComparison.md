## What changed

Filled the five theorem proofs in
`Sheaf.CategoryTheory.Abelian.DerivedInjectiveConeComparison`.
The existing public statements, definitions and imports are unchanged.
Module-local backward elaboration options are recorded in
`coord/changes/DerivedInjectiveConeComparison-transparency.md`.
`tools/downstream.py` reports zero current Lean importers.

The triangle comparison uses the existing inverse-unit boundary theorem,
inverse-unit naturality and reflection of distinguished triangles through the
full faithful inclusion. The cone proof supplies an explicit lower bound and
extends both summand components along a monomorphism to establish injectivity;
Mathlib supplies the two quasi-isomorphisms and the inclusion, negative projection
and quotient identities. Unit naturality at the explicit cone quotient proves
its derived identification. The strict diagonal cone map, localized SES boundary
naturality and componentwise inverse-unit naturality prove both naturality results.
Three proved private helpers implement inverse-unit naturality, the row-triangle
comparison through the inclusion, and lifted boundary naturality.

## Proved and sorry left

Closed all five original holes (node
`lem-pur-derived-injective-cone-comparison`):

- `CategoryTheory.rightDerived_injectiveRow_triangleComparison`
- `CategoryTheory.rightDerived_injectiveRow_coneComparison`
- `CategoryTheory.rightDerived_injectiveRow_coneQuotient`
- `CategoryTheory.rightDerived_injectiveRow_naturality`
- `CategoryTheory.rightDerived_injectiveRow_triangleNaturality`

No holes added, no split-off statements and no sorry left in the delivery.
The entire module compiled through lcompile.py with exit code 0 in 28.6 seconds,
with no compiler warnings. All Lean lines are at most 100 characters.
The proofs use the existing declarations of the node's planned dependencies.

## No longer needed

None. No imports, modules or DAG dependencies were removed. All six numbered
steps of the existing plan are realized, using Mathlib for its standard cone and
SES constructions and the existing right-derived boundary comparison for step 5.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The canonical negative projection and
shift comparisons are retained. Additivity is sufficient: the proof assumes
neither preservation of injectives nor preservation of all quasi-isomorphisms.
The cone injectivity argument uses only the first two complexes; the existing
public signature is preserved. Zero rows and arbitrary integer lower bounds are
covered by the component extension construction and the bound
`min (n₁ - 1) n₂`.

## Forced adaptations

None. The transparency options are module-local proof elaboration settings and
no importer required adaptation.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
