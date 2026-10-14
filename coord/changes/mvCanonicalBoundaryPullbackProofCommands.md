# Proof-local commands for the canonical boundary pullback proof

## Reason

The stage-3 command scanner conservatively reports added universe names and a local
instance attribute as changes to what importers see. Record their exact scope here.
They support the proved private categorical and concrete-SES helpers.

## Old

The item's universe command was `universe u w`. Its global scheme-derived-category
section variable immediately followed `namespace AlgebraicGeometry`. There was no
local priority adjustment for `schemeMVModuleAbelian` and no private helper block.

## New

The universe command is `universe u w v u' v'`; the added names are used only by the
private abstract adjunction helper. The existing scheme-derived-category variable is
placed after the generic private helpers, with exactly its previous type, before the
canonical-boundary helpers and the original public theorem.

`attribute [local instance 2000] schemeMVModuleAbelian` selects the already existing
abelian instance while elaborating the concrete-SES proof. It installs no exported
instance. The heartbeat option for one private naturality theorem is likewise local
to that declaration. All helpers are proved and private.

The original public theorem's signature, universes, visibility, and public imports
are identical. No existing public definition or instance changes. Consequently no
target statement or its meaning changes, and no downstream adaptation is required.
The new public single-open comparison has its own module and DAG node.

## Users

Only the assigned module is edited; its current holder is B2. No other existing
module is adapted. Both delivered modules compile against the published library.

## Status

landed 20261014T013033-L-3412111 2026-10-14 (merge of deliver/B2/Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback)
