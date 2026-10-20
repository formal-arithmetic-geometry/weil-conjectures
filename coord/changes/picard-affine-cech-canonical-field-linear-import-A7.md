# picardExternalCupCoefficients_affine_cech_comparison

## Reason

Restore `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison` from
its current quarantine source after the upstream sync. The rework record reports a
duplicate `AlgebraicGeometry.Scheme.Modules.externalCupCoefficients`: the old public
field-linear import conflicts with the adopted upstream interface used by the proof
dependencies. Import the adopted module directly.

The return of delivery `68760ef877` says the item changed after its base `e0d550965`.
This repair was reconstructed from the current quarantine archive, with both edits
below reapplied, and compiled against the current published build in 12.2 seconds.
The archive and its Lean/DAG attachment remain intact.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The final composite used:

```lean
(HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (.up ℕ) q).mapIso c
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The final composite uses the dedicated homology isomorphism API:

```lean
HomologicalComplex.homologyMapIso c q
```

The public import replacement resolves the duplicate interface. The proof edit avoids
expensive elaboration of the generic homology functor, previously identified by profiling.
Every existing declaration signature, definition body, attribute and docstring is
preserved. The theorem statement is exactly the one recorded on its DAG node.

## Users

A read-only search of both `lean/` and `quarantine/` finds the sole direct importer
below. It is currently quarantined and unclaimed. Its own old public field-linear
import is a separate rework repair, already recorded in `coord/rework.tsv`.
There are no live direct importers requiring adaptation. Other modules listed as
rework dependents are transitive importers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology | unclaimed | Quarantined importer; theorem signature preserved; its obsolete field-linear import requires its separately queued repair. |

No target statement or underlying definition is changed. No source-library file is edited.
No consumer is adapted in this packet.

## Status

landed 20261020T145444-L-2396441 2026-10-20 (merge of deliver/A7/Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison)
