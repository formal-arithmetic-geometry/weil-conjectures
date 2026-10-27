## What changed

Filled all three proof obligations in `Sheaf.CategoryTheory.VaryingSiteSystem`.
Identity compatibility uses functoriality and identity laws. Composition compatibility
uses functoriality, the two given compatibility squares, and associativity.
The category laws follow by subtype and function extensionality from the component
sheaf-category laws. Existing signatures, definitions, docstrings, and imports are unchanged.

## Proved and sorry left

Closed 3 of 3 holes, all attached to `def-per-varying-site-system`:

- `CategoryTheory.varyingSiteSystem_identity_compatible`
- `CategoryTheory.varyingSiteSystem_composition_compatible`
- `CategoryTheory.varyingSiteSystem_category_laws`

No holes remain. No holes or split statements were added.

## No longer needed

None. No proof-dependency imports were needed or added. The node already has no
proof dependencies; its elementary category-law arguments are exactly those of
the existing declaration docstrings. The public imports providing the sheaf
constructions and their typeclass infrastructure remain. No nodes or modules
are withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof descriptions suffice. The arguments work for an empty
index category as well: componentwise extensionality requires no choice of a vertex.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
