# canonicalInternalPush

## Reason

Withdrawn by the reviewer (2026-10-26). The delivery redefined the private
`canonicalInternalPush` and restated the private `canonicalInternalPull_eq`
through `CondensedRing.condensedUpperStarMonoidal`, importing
`Sheaf.Paper.TraceBaseChangeFirst` into the item. That import brings the global
instance `CondensedRing.condensedUpperStarMonoidal` into every module that writes
`import all Sheaf.Paper.ProEtaleSectionModuleFunctors`. There it competes with
`CondensedRing.monoidal_upperStar`: `Sheaf.Paper.InternalOplaxResolvingComponents`
(unclaimed) then fails at lines 365, 369 and 377 (unsolved `rfl` goal, `Type mismatch`
between the two `Monoidal` instances, `simp` heartbeat timeout). The same failure
occurs when only that import is added to the published module.

The reviewer restored the published declarations and proofs of `canonicalInternalPush`,
`canonicalInternalPull_eq`, `canonical_projection`, `internalPullOplax_eq_canonical`,
`internalPull_delta_isIso`, `internalPull_eta_isIso`, `internalPull_preservesFlat`,
`upperStar_tensorπ_delta`, `tensorπ_natural` and their helpers. The item no longer
imports `Sheaf.Paper.TraceBaseChangeFirst`.

## Old

Unchanged: the published text of these declarations.

## New

Identical to Old. No declaration recorded here changes.

## Users

None affected. All 11 direct importers compile against the corrected module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | K9 | Published private pairing kept. |

## Status

withdrawn
