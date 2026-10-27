## What changed
Added two named intermediate statements in the item module: existence of the transported raw localized adjunction and existence of its identity-normalized comparison. The parent theorem now proves its conclusion by applying those statements and unpacking the resulting witnesses.

## Proved and sorry left
The parent declaration `exists_integral_adjunction_raw_localization` is proved by composition. The two strictly smaller intermediate declarations remain `sorry`: `exists_raw_localized_adjunction_core` (node `lem-sf-integral-adjunction-raw-localization-core`) and `exists_raw_localized_identity_comparison` (node `lem-sf-integral-adjunction-raw-localization-identity`).

## No longer needed
None. The existing proof dependencies remain the stated route for the two split obligations.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan expands several substantial localization constructions but does not provide a usable public theorem for the raw finite-Tor functors. The obligations were therefore split at the two construction boundaries while retaining the parent statement unchanged.

## New nodes
`lem-sf-integral-adjunction-raw-localization-core` and `lem-sf-integral-adjunction-raw-localization-identity` are strict sub-obligations: the first constructs only `R`, and the second constructs only `q` after `R` is supplied.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
