# AlgebraicGeometry.ProEtale.prop_of_boundedConstructibleModule

## Reason

Restore the assigned quarantined module after upstream sync 5f7b33eac. Both
proofs called `AlgebraicGeometry.ProEtale.constructible_of_iso`, which is now
private in the extracted UpstreamExtra module. Use the existing proved public
`_root_.constructible_of_iso` from the pullback module, whose coefficient ring
argument is implicit. No definition, statement, universe, visibility or target
changes. The original quarantined file has zero holes; this repair has zero holes.

## Old

```lean
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
```

Both proofs applied `constructible_of_iso R`.

## New

```lean
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
```

Both proofs apply `_root_.constructible_of_iso (R := R)` instead. All public
imports and declaration signatures from the quarantine archive are preserved.
The node retains its Lean attachment and records the shared helper dependency.

## Users

The item is absent from the live Lean tree as recorded in coord/rework.tsv.
A source scan of lean/, quarantine/ and dag/nodes/ identifies the archived tensor
preservation module as its direct consumer. This consumer applies the unchanged
prop_of_boundedConstructibleModule twice, with tensorLeft and tensorRight inverse
image properties. No consumer adaptation is required: all signatures and public
imports are identical. The tensor module has its own upstream-sync repair item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage | C3 | Restore both complete proofs with a direct proof import and the public transport helper. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorPreservation | quarantined repair item | Unchanged public theorem and instance; no source adaptation. |

## Status

landed 20261020T145454-L-2398923 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage)
