## What changed

Added the derived-to-Ext comparison import and proved the main cohomology isomorphism by composing the existing natural derived comparison, the degree-zero Ext-to-sections isomorphism, and a strictly henselian constant-sections natural isomorphism. Added the latter as a named split theorem.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.nonempty_constantSheaf_cohomology_zero_iso`. One sorry remains in `AlgebraicGeometry.Etale.nonempty_strictlyHenselian_constant_sections_natural_iso`; it is recorded by node `lem-sbc-strict-henselian-constant-sections-natural`.

## No longer needed

The direct local-spectrum closed-point argument and the unused pullback-degree-zero import are not needed for the final composition; the existing connected-spectrum and derived comparison APIs supply the route.

## Where the brief, the DAG or earlier work was wrong

The DAG plan omitted the already available natural Ext/derived comparison and did not package the naturality of the constant-section equivalence as a separate Lean declaration. The split theorem records that missing glue.

## New nodes

`lem-sbc-strict-henselian-constant-sections-natural` adds the naturality glue theorem in the item module.
Change record: `coord/changes/strictly_henselian_constant_sections_natural_import.md`.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
