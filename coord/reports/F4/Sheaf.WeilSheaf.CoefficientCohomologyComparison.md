## What changed

The original coefficient_cohomology_comparison statement is unchanged. Its proof now
constructs every C_n by ordinary realization, transport of the Frobenius action,
ordinary cohomology, and restriction to the constructible full subcategory.
It maps the exceptional derived-pair comparison through cohomology, composes with
native_homology, and lifts the resulting isomorphism. The same realization supplies
the Tate endpoint. This is a decomposition, not a hole-free proof of the original theorem.

CoefficientEndpointObjects contains the original Pairs, exceptionalConstant and
twistedConstant definitions verbatim, with the same names; the original module
publicly reexports it. The new placement permits the endpoint lemmas to import these
definitions. The extraction is recorded in
coord/changes/F4-coefficient-endpoint-extraction.md.

NativePairCohomology explicitly defines ordinary derived pairs, their cohomology,
and the ordinary derived Frobenius pair underlying a native Weil complex.
CoefficientRealizationData explicitly constructs the cohomology functors from a
supplied realization. It requires only additivity, shift and Frobenius compatibility,
constructibility and unit normalization. No definition selects a realization from
an unproved existence theorem. The existential witness is unpacked only in the
proof of the original existential proposition.

NativePairHomologyComparison proves compatibility of exact native forgetting with
cohomology, including its Frobenius action, in every degree. The private proof
adapts the cycles/quotient composition calculation from GoodTruncationNormalization
and uses the existing exact-functor natural-isomorphism naturality theorem.
No source-library declaration or target statement is changed.

Validation: all seven delivered modules compiled individually in import order;
NativePairHomologyComparison took 9.9 s and the original item took 6.1 s.
Both direct importers compiled unchanged against this interface:
SmoothCoefficientVanishing (6.4 s) and SmoothDualizingCohomology (20.0 s).
The current server added CoefficientShiftedTateComparison (held by V5) during this
session; that third direct importer also compiled unchanged (7.6 s). All temporary
consumer source copies were removed after the checks. The first broad related-module
check reported 22 OK and 1 INFRA; the new consumer was then checked explicitly.
All seven delivered modules compile without warnings. The final delivery
preflight checks the complete packet again.

## Proved and sorry left

Original holes: 1. Its named theorem
WeilConjectures.NativeCoefficientCohomology.coefficient_cohomology_comparison
now has a complete proof from the two strictly smaller obligations below.
Holes closed in the original module: 1 by decomposition; holes added: 2.
The ledger net (closed minus added) is -1, and the delivered files have two holes.

The following new results and constructions are fully proved:
WeilConjectures.NativePairCohomology.native_homology,
the functor laws of NativePairCohomology.native, and
WeilConjectures.CoefficientRealization.pairCohomology_mem.
All definitions are actual terms and contain no sorry.

Every remaining sorry, each in a separate module with a complete prose proof:

- WeilConjectures.NativeCoefficientCohomology.exceptional_realization
  (lem-sf-exceptional-coefficient-realization): existence of an ordinary unit-normalized
  realization with the exceptional derived-pair comparison. It has neither a
  cohomological degree nor a Tate endpoint.
- WeilConjectures.NativeCoefficientCohomology.realized_tate_cohomology
  (lem-sf-realized-tate-cohomology): the Tate calculation for every supplied realization.
  It constructs no realization and contains no exceptional adjunction comparison.

These separate the two endpoint arguments and retain the explicit functor construction
and native action comparison as proved Lean. Neither is the original theorem renamed
or its hypotheses repackaged. No smoothness has been introduced.

## No longer needed

No existing module or mathematical dependency is globally pruned. All nine old proof
dependencies remain necessary in the two endpoint subarguments or in the native
framework. They are replaced as direct proof dependencies of the main node by the
new construction and comparison nodes, and retained on those nodes where used.

The endpoint-definition module does not import WeilConjectures.WeilSheaf.LowerShriek
or WeilConjectures.WeilSheaf.TateTwist: its definitions use only the coefficient-side
ConstantPurityFrobeniusSquare. The main theorem retains its original public imports;
the exceptional and Tate statement modules import their respective native APIs.
No derived fixed-pair equivalence or smooth-purity comparison is needed for this item.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically retained. Its intermediate realization and endpoint
normalizations did not have the combined interfaces needed by the original theorem.
The two new obligations make those steps explicit. In particular, ordinary derived
pairs must not be identified with the native derived category: the proof constructs
only the forward forgetful functor. The native cohomology action comparison is proved,
not assumed. Full faithfulness and triangulated exactness of the ordinary realization
are unnecessary for this particular interface and are not required in Data.

The returned/quarantined history and current server queue were checked before work.
The current assignment was a one-hole proof-route item, not an import-collision repair.

## New nodes

- def-sf-coefficient-endpoint-objects records the unchanged moved endpoint definitions.
- def-sf-native-derived-pair-cohomology records the explicit native-pair functors.
- def-sf-coefficient-realization-cohomology-data records realization data and the actual
  cohomology construction from it.
- lem-sf-native-pair-homology-comparison records the fully proved native action comparison.
- lem-sf-exceptional-coefficient-realization records the ordinary exceptional endpoint
  obligation, with normalized realization and adjunction-mate proof in words.
- lem-sf-realized-tate-cohomology records the independent generic Tate calculation,
  including shift compatibility, d=0 and the empty scheme.

The main node's proof, proof_deps, proof_origin and Lean declaration list follow the
actual proof. The endpoint definition attachment follows its new module.
Change record: coord/changes/F4-coefficient-endpoint-extraction.md.

## Related modules compiled before delivery

23 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 22 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.WeilSheaf.CoefficientCohomologyComparison": "8851649984ed02b08dbdd34a874e0cde349aaece", "Sheaf.WeilSheaf.CoefficientEndpointObjects": "06771be662eda89ade81334c2859d19130c9e9b3", "Sheaf.WeilSheaf.CoefficientRealizationData": "ba55db137701f8cbc23997eda9a04f3a4315aa25", "Sheaf.WeilSheaf.ExceptionalCoefficientRealization": "5b418bd7e89d6846e399d071dcaa4ca15c9e3e95", "Sheaf.WeilSheaf.NativePairCohomology": "af837f657e0b69d8cc179625511b3fe2713392a5", "Sheaf.WeilSheaf.NativePairHomologyComparison": "c05b2aa158334c82e371d0303e2cffc9155b78ee", "Sheaf.WeilSheaf.RealizedTateCohomology": "7d20884d33489ea162f1bb33bceda00ea5de64c3"}, "results": {"Sheaf.WeilSheaf.CoefficientShiftedTateComparison": {"hash": "b314d8ce29813fe5f997cfc0abac4aa4ccbd2116", "status": "OK"}, "Sheaf.WeilSheaf.SmoothCoefficientVanishing": {"hash": "b221aa52cc66cde14c7bfafadb4d333cfc11be6d", "status": "INFRA"}, "Sheaf.WeilSheaf.SmoothDualizingCohomology": {"hash": "f887bbab45224fe64565d4796d2cef05765ec652", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.Perverse": {"hash": "532f304ad95829a1e4211ea2353c3d601a0bb647", "status": "OK"}, "WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy": {"hash": "07e21eb9c7bc1d1ffa3dc1b3c3734060c970e2d1", "status": "OK"}, "WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed": {"hash": "52e7e5c28569d665cf4735a8ed52c11bfa9a8d65", "status": "OK"}, "WeilConjectures.WeilSheaf.AffineLineCohomology": {"hash": "c2fbfb1465eca69893f01309d2ed3797839bf2d4", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRangeAffine": {"hash": "7841feb68e94c3373f511da11e24c3b2b5c8dc3c", "status": "OK"}, "WeilConjectures.WeilSheaf.LissePoincarePairing": {"hash": "0a3d0391d246d45bfbfbfa8f83fa3bc0fa9bbe4d", "status": "OK"}, "WeilConjectures.WeilSheaf.PoincareDuality": {"hash": "d4162c0bf786ceb2745d5d239fc03852bace16bf", "status": "OK"}, "WeilConjectures.WeilSheaf.PoincareDualityLisse": {"hash": "fe2552db6be2b06e8bc0d4abfa9280a97893fe83", "status": "OK"}, "WeilConjectures.WeilSheaf.TraceIsomorphism": {"hash": "aad7c38032283ba453bba3485d33c699858046c4", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}, "WeilConjectures.ZetaFunction.BettiSymmetry": {"hash": "827e8c634a12023c2dba341fd9f394254454024c", "status": "OK"}, "WeilConjectures.ZetaFunction.DualityReciprocity": {"hash": "d60f1b1d2c3de8f23dde270dab932406ce0edbed", "status": "OK"}, "WeilConjectures.ZetaFunction.Examples": {"hash": "e36146ba0f7231927a1328c607237203746bb899", "status": "OK"}, "WeilConjectures.ZetaFunction.FinalTheorems": {"hash": "3d6504ef77b73dbdab403a3a493962f20a4c0207", "status": "OK"}, "WeilConjectures.ZetaFunction.HasseWeil": {"hash": "123bdc4c708b08a7661d2a5157af692f000eecb5", "status": "OK"}, "WeilConjectures.ZetaFunction.LissePurity": {"hash": "f7605a86dc5093cae7f67578acc1c9f420fe6f9d", "status": "OK"}, "WeilConjectures.ZetaFunction.RealizationIndependence": {"hash": "9e3e6a9829b5ac0703584f754efd3582cec16e16", "status": "OK"}, "WeilConjectures.ZetaFunction.SmoothProper": {"hash": "bff638f34558a3373ae11094cd2307808be83e53", "status": "OK"}, "WeilConjectures.ZetaFunction.Weights": {"hash": "b06fb0c6197e5250f74dc4f6101955ac750c6bb7", "status": "OK"}}, "seconds": 155, "time": "2026-10-28T10:26:20+0800", "transitive": 20, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
