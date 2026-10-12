## What changed

The target theorem now obtains component isomorphisms and their naturality from
`exteriorPresheaf_open_pullback_data`, then packages them with
`PresheafOfModules.isoMk`.  A new module and DAG node provide the component-data
statement; the target node's proof dependencies were updated accordingly.

## Proved and sorry left

The target declaration `exteriorPresheaf_open_pullback` is proved by a complete
construction from the component-data theorem.  The new declaration
`exteriorPresheaf_open_pullback_data` remains a single named `sorry`, recording
the component construction and naturality argument as the next proof item.

## No longer needed

No imports or planned nodes were removed.  The proof uses only
`ExteriorSheaf` and the new component-data module.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan omitted an explicit Lean-level component-data statement;
the categorical assembly through `PresheafOfModules.isoMk` requires that data to
be stated separately.  No target signature was changed.

## New nodes

`lem-sc-exterior-presheaf-open-pullback-data` is added at
`dag/nodes/sec-picard-framework/lem-sc-exterior-presheaf-open-pullback-data.json`.
Its change is implemented by
`Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData`.

## Earlier second reading (a previous round; superseded)

Pending the second reading.  The two sandbox modules compile together, and the
target proof uses the component data only through `PresheafOfModules.isoMk`.

## Second reading by W3

1. Compared both delivered modules and the target node with the repository versions. Existing theorem signatures are unchanged; only the target proof, its proof-only import, and the new component-data declaration/node were added.
2. Compiled both modules with `lcompile.py --all`; the target has no `sorry`, and the sole remaining `sorry` is the named `exteriorPresheaf_open_pullback_data` theorem. No forbidden declarations or hollow definitions were added.
3. Checked the split-off component-data statement against the target: it is a strictly lower component and naturality statement, true by the stated open-immersion section isomorphisms and exterior-power universal property, and has its own node and source docstring. No duplicate declaration was found.
4. Checked the proof route and imports. The target uses `PresheafOfModules.isoMk` with exactly the component data; no old proof dependency or import can be removed, and the unit route through component maps and naturality is retained.
5. Checked DAG agreement: the target node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof, while the new node records the remaining hole, source, and construction route.

Changed during second reading: completed this report section; no Lean proof or statement changes were needed.
