# Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions

## Reason

Human-authorized retirement of the quarantined Sheaf copy in favor of its official
WeilConjectures twin, following the Hand-off in retire-sheaf-twins-20261020.md.
The public transition theorem has exactly the same signature in both modules.
The sole consumer never uses the old private powerSupported_iff helper.
Importing the twin also exposes the current scheme Noetherian API needed by the consumer.

## Old

```lean
import Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions
```

The transition node points to the quarantined Sheaf module. The old module is
quarantine/Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean.

## New

```lean
import WeilConjectures.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions
```

Restore GrothendieckDevissageSecondAdicSystemLiftData at its original Lean path
with this single import replacement. Its statements and proofs remain verbatim.
Point lem-weil-pbc-formal-second-ideal-algebraization-transitions at the twin's
AlgebraicGeometry.formalSecondIdealAlgebraization_transitions, whose signature
matches the quarantined theorem after whitespace normalization.
Withdraw lean/Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean
through deleted.txt. Leave the quarantined text untouched for the maintainer.
No upstream files, target statements, or definitions change. No proof becomes sorry.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftData | unclaimed | Restore from quarantine; replace the transition import; proof unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLift | unclaimed | No declaration changes to adapt; leave quarantine retry to the maintainer. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | No declaration changes to adapt; leave quarantine retry to the maintainer. |

## Status

landed 20261020T153001-L-2858680 2026-10-20 (merge of deliver/E8/Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions)
