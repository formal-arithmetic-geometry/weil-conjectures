## What changed

Repaired the returned module by restoring the complete proof of
`WeilConjectures.NativeCoefficientCohomology.smooth_coefficient_exceptional_vanishing`.
The proof constructs the coefficient smooth-purity pair isomorphism using the
geometric common-stage purity map and its Frobenius square, then transports the
all-degree shifted Tate comparison through the native homology shift vanishing.
The same comparison family supplies the exceptional endpoint isomorphisms in every
homological degree.

Added the strictly smaller module
`Sheaf.WeilSheaf.CoefficientShiftedTateComparison`; its theorem states the remaining
all-degree comparison interface and is intentionally left for a later worker.

## Proved and sorry left

Closed the item's original theorem
`WeilConjectures.NativeCoefficientCohomology.smooth_coefficient_exceptional_vanishing`
(1 of 1 item sorries). The private helper
`coefficient_smooth_purity_iso` is proved as part of the implementation.

Added one strictly smaller split-off sorry:
`WeilConjectures.NativeCoefficientCohomology.coefficient_shifted_tate_comparison`
in `Sheaf.WeilSheaf.CoefficientShiftedTateComparison`.

## No longer needed

The old direct proof dependencies `lem-sf-adic-qbar-constructible-realization` and
`cor-pur-adic-and-rational-smooth-dualizing-complexes` are no longer direct proof
inputs. The proof uses the existing coefficient comparison, the rational smooth
purity map and Frobenius square, the smooth base-change permanence declaration, and
the new all-degree shifted Tate comparison. No existing source module or declaration
was removed.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan treated off-degree vanishing of the coefficient Tate endpoint
as automatic from an existential comparison family. That family only exposed the
exceptional comparison and the surviving Tate degree. The split-off theorem records
the missing all-degree normalization explicitly, so the completed item can transport
zero objects without assuming properties of an arbitrary witness.

## New nodes

`lem-sf-coefficient-shifted-tate-comparison` records the all-degree native comparison
for shifted Tate constants before imposing smoothness. Its Lean theorem has a complete
source and proof description in its docstring and one named `sorry` as required for a
strictly smaller unresolved step.

## Related modules compiled before delivery

34 related module(s) compiled against this delivery by deliver3.py: 31 OK, 3 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.CoefficientShiftedTateComparison": "b314d8ce29813fe5f997cfc0abac4aa4ccbd2116", "Sheaf.WeilSheaf.SmoothCoefficientVanishing": "b221aa52cc66cde14c7bfafadb4d333cfc11be6d"}, "results": {"Sheaf.Paper.CurveMiddleExtensionUpper": {"hash": "c6f8dfc1e80926b9a264bde2f1d573a678b9a70a", "status": "OK"}, "Sheaf.WeilSheaf.SmoothDualizingVanishing": {"hash": "c139d3826d04573d7713ce9d367e8ab94ef09cc7", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper": {"hash": "25e17f64018e0dd56a69ea571797e24d9dca8518", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform": {"hash": "c268069b6605a2f643c4277583a0dd05e3b61c65", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist": {"hash": "56b09c11f9acc0b083ba686f416eb107d8ffde92", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.AffineLine.Exactness": {"hash": "4af5d2f065444ee1c1bb8d8d80f464fdc4ee52ce", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude": {"hash": "a3f2bb005144566b73d2d85c1b584f7eadcd3d00", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport": {"hash": "921280e6e46c895b53991bdb4a9c3b05548dfe03", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.LocalDuality": {"hash": "362511fd1ec8ffac6035ff8ce532c2e19daa78d9", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension": {"hash": "9753b98e1fa5ec93f971192c482a58102b4fde9e", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform": {"hash": "0d7dbae6f69ef36fd481f1c3239ee3c5366e8e49", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.Upper": {"hash": "4872917439f2f273858ff87df6ab15b30db2c9b4", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.UpperReduction": {"hash": "e3f8b4d6e1faf26a97c6671730fd3a7c71b29b48", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.Reduction.AffineCurve": {"hash": "8bb655d0a4f6a82fcfdd1ed5a7b1fb5e7238ddac", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.DirectImage": {"hash": "9246cfbabe1a4bc9d3bb351a15113408b707b89b", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension": {"hash": "540ce6b39bccc3c943bd009279b59bf301d7a606", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.OpenLine": {"hash": "70ee63c95ed3689548187b04daf0db07170ccc08", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.RealSheaves": {"hash": "3d3491027e07ee3e2dd18fc3df95caa6869d9eb7", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine": {"hash": "6c73b57001b8950cc7f31da4c2f731db4903d590", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep": {"hash": "301553d7976da0fc4df0d21f957694e6eb9dd812", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants": {"hash": "a8831739817950f0331524f4c1e6694204689c9a", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional": {"hash": "9844113c4552da8f05f5250deb8fff57104df02b", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension": {"hash": "1cf2209f21aed0e231dd7e13c6fc77f6bb61f478", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity": {"hash": "25e6ab1b83aba88d7e8a761e1e92bb9bcc1a03ed", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity": {"hash": "cdb3223783897af1559b130b1ce31daeef4173a7", "status": "OK"}, "WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary": {"hash": "ffe03e4cd28e4f739a2f1219a1d8fbe04930691a", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRange": {"hash": "6ca2482878f1da28c25673e03e74340fbf93acdd", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRangeAffine": {"hash": "7841feb68e94c3373f511da11e24c3b2b5c8dc3c", "status": "OK"}, "WeilConjectures.WeilSheaf.CurveEndpoints": {"hash": "a34bf6b1522712199f815703144df1c0e606f3ab", "status": "OK"}, "WeilConjectures.WeilSheaf.RealPurity": {"hash": "f1d064ef649328d0668c47418d2639a92883d27a", "status": "OK"}, "WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity": {"hash": "a044b657bf5c50ba6e92c2715c05a668c83e7f02", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDualLocalization": {"hash": "8d0fd3ed2a48117c97e67305db2be09cdb6189b4", "status": "OK"}, "WeilConjectures.ZetaFunction.RelativePurity": {"hash": "4f8c68373735a415ba035c6c4c9e1e3c3cfbac31", "status": "OK"}}, "seconds": 231, "time": "2026-10-28T09:45:52+0800", "transitive": 33, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
