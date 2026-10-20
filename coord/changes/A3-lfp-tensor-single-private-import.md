# Restore the LfpTensorSingle proof after the upstream sync

## Reason

The `coord/rework.tsv` assignment preserves this module at
`quarantine/Sheaf/AlgebraicGeometry/LfpTensorSingle.lean`. Its recorded compiler error
is an unknown identifier `locallyFinitelyPresented_of_isZero` in the integral
calculation's `ContainsZero` proof. The private helper moved out of the adopted
upstream module during the sync into
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.

## Old

The archive imports the old location with `import all`, and imports the new
location publicly without private-name access.

## New

Restore the archived module and replace only its private proof import
`import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`
by
`import all Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
The existing public imports, declaration signatures, proof bodies and definitions
are retained verbatim. No upstream file changes. There are zero direct sorry holes.
The existing node `lem-sfb-lfp-tensor-single`, its attachment and its dependencies
are preserved. The mathematical argument is unchanged.

## Users

Searching both `lean/` and `quarantine/` for the module and `lfp_tensor_single` finds
one Lean consumer: the quarantined
`Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle`, at the two applications
of `lfp_tensor_single`. Its theorem applications and public context are unchanged;
no consumer adaptation is needed. The node remains needed by that parent's proof,
regardless of the parent's current quarantine status.

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | A3 | Restore and repair private proof import. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | Not edited | Identical theorem interface; no adaptation. |

## Status

landed 20261020T154933-L-3173842 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.LfpTensorSingle)
