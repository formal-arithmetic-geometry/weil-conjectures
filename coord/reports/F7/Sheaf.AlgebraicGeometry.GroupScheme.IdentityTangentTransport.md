## What changed

Retired `Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport`, listed in
`coord/retire-items.tsv` as a DIFFERENT twin, by removing its duplicated existential
theorem `AlgebraicGeometry.GrpObj.exists_identity_tangent_transport`. The adopted
source already provides the required equivalence as `identityTangentTransport`
and its exact morphism formula as `identityTangentTransport_val`.

Adapted its sole caller,
`Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv`, to import upstream
transport privately and use that construction and equation directly. Its proof
still combines transport, operation compatibility, and lieEquiv.symm; its exact
statement, visibility and public imports remain unchanged. No source-library
file changes. The transport node attaches to both upstream declarations, and its
parent node records their direct use. All mathematical dependency edges remain.

Change record: `coord/changes/F7-identity-tangent-transport-retirement.md`.

## Proved and sorry left

There were zero direct holes in the current item before this delivery; zero
remain. Holes closed: none. Holes added: none. Split off: none. This is a
retirement of duplicated proved code, not a new hole closure or decomposition.
The adapted `AlgebraicGeometry.GrpObj.exists_lie_identity_tangent_linearEquiv`
remains fully proved with its original statement.

The original item compiled. A compatibility-wrapper proof using the upstream
construction and equation also compiled, as did the caller against that proof.
The final delivery goes further: the caller uses the upstream declarations
directly, so the intermediate wrapper and its module can be withdrawn entirely.
The final adapted caller and its unchanged downstream LieCotangentDual both
compiled individually through lcompile.py --all. The existing upstream formula
preserves every prescribed coefficient and map;
no new statement or definition is introduced.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.GroupScheme.IdentityTangentTransport`.
Its caller removes that proof import and imports
`WeilConjectures.AlgebraicGeometry.GroupScheme.IdentityTangentTransport` instead.
The duplicate declaration `exists_identity_tangent_transport` is no longer needed.
The replacement argument is in the same delivery: explicit upstream witness and
its defining formula, followed by the unchanged linearity proof.

No DAG node is deleted. `lem-ag-identity-tangent-transport` remains needed and is
reattached upstream. The identity-residue rationality and tangent-space definition
dependencies remain needed by the upstream construction. This prunes a module,
not those mathematical dependencies or their source declarations.

Repository-wide Lean and DAG searches, including quarantine, found one direct
Lean caller and one DAG parent, both accounted for. No unit route is bypassed.
The downstream LieCotangentDual theorem still sees the unchanged parent interface.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished proof and earlier splits, but the
current item is already sorry-free and is listed in the retirement inventory.
The inventory's reason for retaining it was that upstream lacks the existential
wrapper name. Upstream nevertheless provides the complete construction and exact
formula; adapting the caller removes the need for that name. The source-library
boundary is respected: no upstream declaration, body, attribute or import changes.
No current return or rework entry for this item was found.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
