# Retirement of Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde

## Reason

Apply the human-approved retirement in `retire-sheaf-twins-20261020.md`, Hand-off.
The official twin proves the same affine associated-sheaf K-flatness theorem.
Its conclusion is called `CochainComplex.IsKFlatTensor`, definitionally equal to
`CochainComplex.IsAcyclicTensorKFlat` used in the existing consumers. No consumer
signature, definition, upstream file or target statement changes. Some local
instance proof binders are inlined to avoid single-file compile timeouts. The
affine derived-pullback consumer also extracts only the tensor-counit part of
the pullback specification, following the official module, and uses a proved
private wrapper for the old K-flat predicate. Local instance priorities select
the existing scheme category, abelian, limit and colimit instances. The
mathematical proofs and all public interfaces are preserved.

## Old

Consumers imported `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde` (publicly in
`QCohTensorResolutionAffineModel`). Node `lem-pc-affine-tilde-kflat` pointed to that
module and its declaration `AlgebraicGeometry.isKFlat_tilde`.

```lean
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
```

## New

Replace each of those imports by
`WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde`, with the same visibility.
Keep the theorem name and all consumer signatures. Repoint the node's module,
file and recorded conclusion name to the official twin. Withdraw
`lean/Sheaf/AlgebraicGeometry/Modules/IsKFlatTilde.lean` through `deleted.txt`.

```lean
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
```

The public import in `QCohTensorResolutionAffineModel` likewise retains `public`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde | unclaimed | Replace proof import; inline local instance proofs; prefer existing scheme-module instances; use explicit reducibility settings with the original settings scoped to the two private comparisons and the base-change bridge application that need them; extract the tensor-counit specification; prove a private predicate-conversion wrapper; explain the style-linter exception. |
| Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison | unclaimed | Replace proof import; existing proof call compiles unchanged. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionAffineModel | unclaimed | Replace public import; wrap one long signature line and use proof-irrelevant `let`/`have` binders to clear existing style warnings. |

These are all live source consumers. The other ten modules in the dispatcher
inventory are absent from the current `lean/Sheaf` tree and need no file edits.
No upstream source file imports the retired module. Historical `created.item`
records in other nodes are provenance, not live module attachments or imports.
All three consumers compiled through `lcompile.py`; no proof was replaced by
`sorry`, and no new public declaration or data definition was introduced.

## Status

landed 20261020T145541-L-2410468 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde)
