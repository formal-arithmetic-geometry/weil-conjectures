## What changed

Proved `AlgebraicGeometry.Scheme.cbcFiniteInverse_isIso` in
`Sheaf.Paper.CompletedRingStrictFiniteExchange`. Install the square's two open-immersion
instances, recover its `IsPullback` proof with `IsPullback.of_iso_pullback`, and apply the
existing `AlgebraicGeometry.ProEtale.StrictTower.singleBetaInv_isIso`. Whiskering this
isomorphism by finite scalar restriction gives the stated instance.

All declaration signatures and definitions are unchanged. This is a partial delivery of
one of the module's three existing holes, with no split-off statements. The module compiled
cleanly with `lcompile.py` (14.4 seconds). Earlier compile requests received the documented
busy-server response; the successful compile checked the final file.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.cbcFiniteInverse_isIso`.

Two existing holes remain, both attached to
`lem-cbc-completed-ring-strict-finite-exchange`:

- `AlgebraicGeometry.Scheme.cbcFiniteComparisons_existsUnique`.
- `AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange`.

Added zero holes. The completed finite inverse proof uses the existing finite-ring
finiteness instance and finite open-base-change theorem; their own dependencies are not
claimed to be axiom-free by this delivery.

## No longer needed

Removed these unused direct private proof imports from the item:

- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.

No public import was removed. No module or DAG dependency is withdrawn: the two remaining
holes retain their existing plans, and these modules also occur in the coordinate module's
proof imports. There is therefore no claim of whole-module pruning from the targets.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The finite inverse instance follows exactly its existing
proof plan. The other two holes are not discharged by the finite inverse theorem: their
normalizations involve the specified universal counits and the finite coordinate mates.
The available finite-evaluation and strict-reduction interfaces use additional coefficient
coordinates; their normalized compatibility still requires proof. No arbitrary comparison
isomorphism was substituted for a normalized one, and no statement was weakened.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
