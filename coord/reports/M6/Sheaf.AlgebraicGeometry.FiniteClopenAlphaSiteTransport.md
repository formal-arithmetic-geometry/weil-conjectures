## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.finiteClopenAlphaSiteTransport`
by an assembly of the two specified sheaf factors and a complete exact-localization
argument. The latter proves the unit factorization of exact right-derived base
change, identifies it with the prescribed localized square, and specializes the
existing right-derived-plus cube. Naturality and cancellation identify all four
canonical site comparisons and the actual proetale alpha.

Added `FiniteClopenBetaSiteTransport` and `FiniteClopenTailSiteTransport` for the
two remaining geometric steps. The tail statement displays the etale projector and compositors explicitly;
the proetale tail is their real whiskered composite. The proof applies the etale
component API directly, avoiding an expensive equality between duplicate tail
constructions. No arbitrary object is chosen. The beta lemma is independent of properness, the other open, and derived categories.

Added three proved public component/factorization wrappers to the unclaimed
`EtaleClopenMateNormalization` module. Existing declarations, imports, definitions,
attributes, and statements stay byte-for-byte unchanged. The change record is
`coord/changes/M6-etale-clopen-normalization-component-api.md`.
The adapted normalization module and all six original direct importers compile
successfully through `lcompile.py`; no consumer source adaptation was needed.
Temporary unchanged consumer copies were removed after these checks. The final
beta and tail modules and the item also compile through `lcompile.py`; the item
passes in 54.6 seconds (result `1e43cb1c7d533c87a2db3d2b`). All profiling options
and scratch modules were removed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.finiteClopenAlphaSiteTransport`
(node `lem-cbc-finite-clopen-alpha-site-transport`) by decomposition.

Added two holes, both public named theorems with complete source proofs:

- `AlgebraicGeometry.ProEtale.finiteClopenBetaSiteTransport`
  (`lem-cbc-finite-clopen-beta-site-transport`).
- `AlgebraicGeometry.ProEtale.finiteClopenTailSiteTransport`
  (`lem-cbc-finite-clopen-tail-site-transport`).

The item's module has zero remaining holes; the packet adds two. This is a
one-to-two decomposition, not a net proof gain. All localization and assembly
helpers, and all three added component API lemmas, have complete Lean proofs.
The generic derived cube is an existing proved declaration. No definition or
private helper contains `sorry`.

## No longer needed

No original public import is removed: all four are needed by the unchanged public
statement. No module is globally pruned. The original geometric dependencies
`cor-cbc-derived-extension-zero-base-change`,
`lem-cbc-proetale-extension-zero-base-change`,
`lem-cbc-proetale-extension-zero-comparison`, and
`def-weil-pbc-adjunction-mate` remain needed below the two factor statements.
The item also directly uses the etale normalization's new component API and the
canonical pullback comparison. The generic localization calculation replaces no
unit statement or unit proof step.

## Where the brief, the DAG or earlier work was wrong

The planned geometric steps do not already have the needed site-compatibility
signatures: the stated extension comparison gives composition/identity, and
base-change nodes supply the maps, but neither states transport of inverse beta
or the clopen projector. Those are precisely the two new factor statements.

The etale exact localized square and alpha definitions hide their bodies from
importers; their component calculations were private. The proof therefore needs
proved public API wrappers. No mathematical statement was changed or disputed.
The new statements were checked for empty image, empty complement, identity open,
and arbitrary (not necessarily proper) p in the beta lemma.

## New nodes

`lem-cbc-finite-clopen-beta-site-transport` is the open-unit transpose step of the
original node, on ordinary sheaves and an arbitrary cartesian open square. It
contains neither the clopen projection nor any localization.

`lem-cbc-finite-clopen-tail-site-transport` is the identity/zero projection and
outgoing-compositor step. Its source is the cartesian-open term J_b G_q, not
G_p J_i; it contains neither cartesian base change nor derived localization.
The item multiplies their equalities and proves the derived step in Lean.

Three existing nodes gain attachments for proved component APIs; no source route
or unit is changed. Change record:
`coord/changes/M6-etale-clopen-normalization-component-api.md`.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
