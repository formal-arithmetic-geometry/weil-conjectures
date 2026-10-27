# WeilConjectures.DiagramPullbackShift.rings and transitions

## Reason

Restore the full quarantined module for its assigned rework row. The recorded global-build
error at the constant-sheaf application is an unsolved universe constraint involving
`HasSheafify (ProEt.topology W) CommRingCat.{max ?r (u + 1)}`. The imported canonical
instance is parameterized by an independent coefficient universe, which cannot be inferred
backwards from this maximum. Select its specialization `integralCoefficientRingSheafify.{u, u}`
explicitly inside both definitions, before elaborating `constantSheaf`.

This does not change the coefficient ring universe, the constant-sheaf construction,
the sequence site, the ring transition maps, or any public signature. `HasSheafify` is a
proposition, so its instance proofs are definitionally equal by proof irrelevance.
The same construction is used in both definitions. No new public declaration or local
instance leaks into consumers. No target changes meaning or needs a mathematical
statement correction; this is an elaboration repair.

## Old

The archived declaration block was:

```lean
def rings (W : Scheme.{u}) (n : ℕ) : Sheaf (ProEt.topology W) CommRingCat.{u + 1} :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj (A n)

/-- The actual constant-sheaf images of the adjacent coefficient homomorphisms.
Source: Zheng Construction 4.1
(blueprint: def-pur-diagram-pullback-shift-data). -/
def transitions (W : Scheme.{u}) (n : ℕ) : rings A W (n + 1) ⟶ rings A W n :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map (δ n)
```

## New

```lean
def rings (W : Scheme.{u}) (n : ℕ) : Sheaf (ProEt.topology W) CommRingCat.{u + 1} :=
  letI : HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u} W
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj (A n)

/-- The actual constant-sheaf images of the adjacent coefficient homomorphisms.
Source: Zheng Construction 4.1
(blueprint: def-pur-diagram-pullback-shift-data). -/
def transitions (W : Scheme.{u}) (n : ℕ) : rings A W (n + 1) ⟶ rings A W n :=
  letI : HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u} W
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map (δ n)
```

Every other byte of the restored Lean module agrees with the quarantined source.

## Users

`tools/downstream.py Sheaf.SixFunctors.DiagramPullbackShiftData --allow-missing --uses
rings transitions` reports zero current library consumers because these files are quarantined.
The archived import graph has the following consumers. Claim holders below are from the
shared local snapshot; the remote delivery checks the current server claims. Their sources
are not modified or withdrawn by this repair.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.DiagramGeometricTensorPresentations` | unclaimed in local snapshot | Direct archived importer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels` | unclaimed in local snapshot | Direct archived importer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.DiagramTensorPullbackShiftDescent` | unclaimed in local snapshot | Direct archived importer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.DiagramTensorShiftConstraints` | unclaimed in local snapshot | Direct archived importer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |
| `Sheaf.SixFunctors.SystemTensorShiftCoherence` | unclaimed in local snapshot | Archived transitive consumer; signatures and meaning preserved; no adaptation |

The existing DAG attachment `def-pur-diagram-pullback-shift-data` is retained verbatim.
Its definition statement, dependency edges and the fixed unit route are unchanged.

## Status

landed 20261026T001950-L-45606 2026-10-26 (merge of deliver/M1/Sheaf.SixFunctors.DiagramPullbackShiftData)
