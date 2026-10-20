# Retire the duplicate open-module stalk restriction comparison

## Reason

The retirement queue assigns Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison.
Its theorem asserts existence of a natural isomorphism which the source library now
constructs explicitly as Scheme.openModuleStalkRestrictionComparison. Keeping the local
germ argument duplicates the source construction.

## Old

 AlgebraicGeometry.Scheme.nonempty_openModuleStalkRestrictionComparison in
Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison returns Nonempty of the
comparison type. Its six private supporting declarations duplicate the source argument.

## New

Both callers use AlgebraicGeometry.Scheme.openModuleStalkRestrictionComparison
from WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison directly.
The parameters, universes and natural-isomorphism type agree exactly, without added
hypotheses. OpenStalkRestrictionTransport no longer chooses an isomorphism from Nonempty;
PerfectOpenStalkDegreewiseShrink binds the explicitly constructed isomorphism.
The Sheaf copy is withdrawn via deleted.txt, and its node points at the source definition.
No source-library file or target statement changes.

## Users

- `Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport` (unclaimed): replace its private
  proof import and the single comparison use. Its theorem signature is unchanged.
- `Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink` (unclaimed): replace its private
  proof import and the single comparison use. Its theorem signature is unchanged.
- `Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift`: indirect user; the unchanged public
  transport statement is still available.
- `Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift`: indirect user; unchanged interfaces.
- `Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift`: indirect user; unchanged interfaces.
- `Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent`: indirect user; unchanged interfaces.
- `Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift`: indirect user; unchanged interfaces.
- `Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection`: indirect user; unchanged interfaces.

The retirement inventory also names OpenOrdinaryTensorPureGermCoordinatesCanonical and
OpenStalkUnitMapOneLiftBridge. Those Sheaf files have already been retired in the current
tree, and their source counterparts already import the source comparison.
All existing importers and uses of the removed public theorem were searched in both roots.

## Status

landed 20261020T141315-L-2035838 2026-10-20 (merge of deliver/S6/Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison)
normal delivery preflight and independent review follow. There are zero textual holes
before and after, and none are added by retirement.
