# pageTwoComparison module move

## Reason

The proof-support theorem `exists_unique_pageTwoMap` must mention the canonical
comparison while remaining importable by the target without a cycle. The
comparison definition therefore lives in its own support module and is publicly
re-exported by the target module.

## Old

`pageTwoComparison` was defined in
`Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor`.

## New

`pageTwoComparison` is defined in
`Sheaf.CategoryTheory.SpectralObjectPageTwoMap`, which the target module publicly imports.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CartanEilenbergPageRealization | unclaimed | Public import through the target remains unchanged. |
| Sheaf.CategoryTheory.CartanEilenbergFilteredTruncationComparison | unclaimed | Public import through the target remains unchanged. |

## Status

landed 20261015T221711-L-2641190 2026-10-15 (merge of deliver/K2/Sheaf.CategoryTheory.SpectralObjectPageTwoFunctor)
