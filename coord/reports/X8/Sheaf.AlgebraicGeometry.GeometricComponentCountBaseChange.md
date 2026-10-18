## What changed

Proved `AlgebraicGeometry.geometricComponentCount_baseChange` in
`Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange`, with its signature and
imports unchanged. Three proved private helpers transport component counts across scheme
isomorphisms, turn the stated separably closed component bijection into an equality of
`ENat.card`, and compare two algebraically closed extensions in a common extension.
Mathlib's `pullbackLeftPullbackSndIso` and residue-field naturality then give arbitrary
base change. The proof follows Stacks Tag 055F and the existing DAG plan; it uses the
existing `Field.exists_common_extension` and
`bijective_connectedComponentsMap_pullback_fst_of_isSepClosed` declarations.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.geometricComponentCount_baseChange`
(node `lem-weil-pbc-geometric-component-count-base-change`). Added 0 holes and split off
0 statements. No `sorry` remains in the delivered module. The existing dependency
`AlgebraicGeometry.bijective_connectedComponentsMap_pullback_fst_of_isSepClosed` remains
an independently assigned theorem; this delivery uses its unchanged statement.
The equivalences impose no finiteness or nonemptiness assumptions, so empty fibres and
infinitely many components are covered by `ENat.card_congr`.

## No longer needed

None. No imports, dependency nodes or modules were pruned. All existing proof
dependencies are used, and no extra imports or nodes are needed. The unit's route is
unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The declared dependency interfaces suffice. The proof
uses explicit `Scheme` annotations for pullbacks inside `ConnectedComponents` to avoid
Lean inferring pullbacks in the category of types. Searches found `ENat.card_congr` and
the pullback-pasting API, but no theorem that directly replaces the planned argument.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
