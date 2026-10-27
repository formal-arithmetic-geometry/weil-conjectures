## What changed

Filled `WeilConjectures.SemilinearSections.blockOpenExtensionComponent_transition`
in `Sheaf.Paper.BlockOpenExtensionTransitions` by the ordinary localized
adjunction. The proved calculus in the new proof-only import
`Sheaf.Paper.OpenSystemUnitSections` extracts the evaluated unit formula, shows
that maps from an evaluated extension are determined on those unit sections,
and the item's private helpers compute the component comparison on the units. Naturality of the original
and repeated system units, together with `hQ`, `hqev`, and
`R.repeat_restrictions`, then proves the horizontal equation.

Private carrier-transport lemmas first identify the section types of continuous
module pushforward. Their explicit casts avoid expanding the large coefficient
system and sheafification terms during the unit normalization; they preserve
the actual sections and restriction functions.

All four existing public declaration signatures, both definition bodies, and
both public imports are unchanged; the support import is private. The coefficient constructions are locally
irreducible during proof elaboration, with transparency checks enabled. No
existing shared module, instance, definition, or exported attribute changes. The item's
DAG proof records this direct adjunction-unit argument.

Validation: `lcompile.py --all` compiled both files without errors or warnings:
`OpenSystemUnitSections` in 37.4 s and `BlockOpenExtensionTransitions` in 41.5 s.
The four existing public signatures remain unchanged, and both files contain
zero `sorry` tokens.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.blockOpenExtensionComponent_transition`
(node `lem-pur-block-open-extension-transitions`).

Holes closed: 1. Holes added: 0. Split-off statements: 0. Sorries left in the
item or support module: none. The support criterion
`WeilConjectures.SemilinearSections.OpenUnitSections.open_level_hom_ext_raw`
and all carrier-transport and normalization helpers are fully proved. This is
a proof, not a decomposition into additional unproved statements.

## No longer needed

None. Both original imports are required by the existing public signatures;
both original proof dependencies remain in use. No module or DAG node is
withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The direct-sum generator argument in the DAG
can be implemented through injectivity of the existing ordinary adjunction Hom
equivalence: the supplied unit evaluation identities already identify exactly
the generators needed for the test. This avoids reconstructing the direct-sum
presheaf or sheafification. The proof works for non-flat coefficient maps,
zero rings, identity repetitions, singleton blocks, and horizontal arrows
inside a block, since it uses only the supplied unit and restriction formulas.

## New nodes

`lem-pur-open-system-unit-sections`, realized by
`Sheaf.Paper.OpenSystemUnitSections`, proves the ordinary unit-generation
criterion and its carrier-transport calculus. Its statements contain no block
repetition data and are strictly the unit-normalization part of the argument.
The coefficient constructions were first protected with explicit generic
carrier transports. The resulting monolithic proof checked but took 68 seconds;
extracting this already-proved calculus follows the current worker brief's
step 3a and keeps the files under the single-file compile limit. It adds no hole
and changes no existing statement or definition. No change record is needed.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
