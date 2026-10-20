## What changed

Retired `Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections`, the zero-hole
duplicate assigned by `coord/retire-items.tsv`. Its one consumer,
`Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap`, now privately imports
`WeilConjectures.AlgebraicGeometry.PicardConstantTensorBalancedSections`. The proof binds
its balanced equivalences directly to `picardConstantTensorBalancedSections`, and its
scalar-action and restriction laws to `_smul` and `_map`. All subsequent proof steps,
its theorem signature, and all public imports remain identical. The adapted module
compiled successfully in 10.3 seconds through `lcompile.py`.

Reattached `lem-sc-picard-constant-tensor-balanced-sections` to the upstream construction
and its two laws. Updated its proof origin and its sole parent's proof text to record
the migration; mathematical statements, proof dependencies, and unit route stay intact.
No source-library file is changed. Change record:
`coord/changes/R2-retire-picard-constant-tensor-balanced-sections.md`.

## Proved and sorry left

The assigned module starts with zero `sorry`: closed 0 of 0 holes, added 0 holes,
split off 0 statements, and left 0 holes. Its already proved theorem
`AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections` is
retired in favour of the explicit upstream construction and its proved laws.
`AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_map` retains
a complete proof with no `sorry`. This is a retirement, not a new proof or decomposition.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections`.
Removed private import: that module from `ExternalConstantSectionsTensorMap`.
Removed declaration: its duplicate `exists_picard_constant_tensor_balanced_sections`.
The upstream construction and `_smul`/`_map` declarations replace its entire role.

No DAG node or mathematical proof dependency is pruned. In particular,
`lem-sc-picard-constant-scalar-extension-sections` remains needed by the retained
upstream construction, and the parent retains its balanced-sections dependency.
The duplicate module's imports of upstream `PicardConstantSectionsTensor` and
`PicardConstantScalarExtensionSections` remain needed upstream.

Searches of all Lean and quarantined sources found exactly the adapted consumer and
no remaining uses of the withdrawn name. The only DAG parent was checked and updated;
`sk-prop-av-cube` has no realized attachment to this module, so its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished chain, but this current assignment is
listed as `retire`, with a fully proved source module. The retirement census says the
upstream twin lacks the existential name; its named construction and two laws already
provide exactly that mathematical content. Reusing them requires no new theorem,
weakened statement, postponed proof, or change to a definition. There is no current
return or quarantine row for the item.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
