## What changed

Retired `Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections`, the zero-hole
retirement item listed in `coord/retire-items.tsv`. Its full private scalar-extension
implementation duplicates the adopted-source module of the same final name. The latter
provides explicit `picardConstantScalarExtensionSections` and the proved restriction law
`picardConstantScalarExtensionSections_map`.

Migrated the sole direct consumer,
`Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections`, by changing its private
import, binding its local `q` to the upstream construction, and replacing its old
existential witness's restriction law with the upstream map theorem. Its existing theorem
signature, public imports, docstring, and all other proof steps are preserved. No adopted
source file is changed. The original scalar-extension comparison node now records the
upstream construction and map law, and its parent's first proof step records the migration.
The node statements, dependencies, and unit route are preserved.

Change record: `coord/changes/Q1-retire-picard-constant-scalar-extension-sections.md`.

## Proved and sorry left

Original holes: **0**. Holes closed: **0**. Holes added or split off: **0**.
No `sorry` remains in any delivered Lean source. This is a duplicate retirement, not a
new proof of an open theorem. The already-proved existential declaration
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_scalar_extension_sections`
is retired with its implementation; the consumer now obtains that data and its law
directly from the already-proved adopted-source declarations.

The migrated `AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections`
compiles cleanly through `lcompile.py` (5.3 seconds). The unchanged indirect consumer
`AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map` also
compiles against the migrated module (13.9 seconds). The original item compiled
cleanly before retirement (8.2 seconds). Delivery checks run the transitive axiom
probe on the migrated consumer.

## No longer needed

- Module `Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections` is withdrawn
  using `deleted.txt`; its sole private importer is migrated in this packet.
- Its duplicate private definitions `extensionRestriction`, `extensionPresheaf`,
  `extensionToRestrict`, `extensionFromRestrict`, `extensionHomEquiv`, and
  `extensionCorepresentableBy`, and the private `extensionRestriction_tmul` theorem,
  are removed with it. The adopted-source equivalents remain verbatim.
- The consumer's private import of the retired module is replaced by
  `WeilConjectures.AlgebraicGeometry.PicardConstantScalarExtensionSections`.
- No mathematical DAG node or proof dependency is pruned. The comparison node remains
  needed by its parent and is realized by the upstream construction and restriction law.
  The scalar-extension Hom equivalence and constant-ring definitions are still used by
  the preserved upstream proof. No unit statement or step is bypassed.

Local library and quarantine searches find one direct Lean importer and one DAG parent,
`lem-sc-picard-constant-tensor-balanced-sections`; both are handled here. The indirect
consumer `Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap` requires no edits.

## Where the brief, the DAG or earlier work was wrong

The generic opening described an item with `sorry` or an assigned repair. This item has
zero holes and is specifically listed for retirement. The inventory says the upstream
twin lacks the old existential theorem, which is literally true; it nevertheless exposes
the same equivalences as actual data, together with precisely the required restriction
law. Thus no new theorem, arbitrary existence choice, statement weakening, or additional
proof obligation is needed. The original DAG proof is valid and survives in the upstream
module; only its Lean attachment and its consumer's API use need to change.

Searches performed through `msearch.py`: LeanFinder for pointwise scalar extension
returned presheaf/tensor ingredients, Loogle did not index the upstream name, and the
Mathlib grep search returned no matching name. Direct `rg` searches in both project roots
located the exact upstream construction and law. Reading their entire implementation
confirmed the same tensor presheaf and representing-object argument, including the zero
module and empty-open cases. The dependency declarations and the unit record were read;
this migration preserves the unit route and the original theorem's full generality.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
