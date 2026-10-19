# Sheaf.Paper.DenseOpenPiOneSurjective proof scope

## Reason
The proof replaces the original sorry bodies with explicit helper theorems and a shorter
route through the existing normal dense-open and restriction APIs. This changes proof-local
commands and imports visible while importing the module, so stage 3 requires a change record.
No public theorem signature or definition is changed.

## Old
The module had the same eight public theorem signatures with `sorry` proofs, and imported
the open-subgroup, representation-equivalence, and normal-decomposition proof modules.

## New
The module proves all eight existing declarations. It imports the source normal dense-open,
finite-level unit, Weil-sheaf dense-open, and restriction APIs, plus faithfully-flat algebra
lemmas; it adds a local irreducibility attribute and private helper theorems. The public
signatures and their meanings are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Imports the proved declarations; no signature or source change needed. |
| Sheaf.Paper.RealSheafSections | unclaimed | Imports the proved declarations; no signature or source change needed. |

## Status
landed 20261019T231122-L-549663 2026-10-19 (merge of deliver/E3/Sheaf.Paper.DenseOpenPiOneSurjective)
