## What changed

Proved both theorems in `Sheaf.Paper.RationalP1SecondPullSection` without changing
their statements. The untwisted theorem packages the existing core equation. The
full theorem constructs the residue-field invertibility instances, obtains the existing
Tate transport data, applies the proved generic `pull_section_transport` calculation
to the untwisted equation, and rewrites the canonical comparison by its existing
inverse-map expansion. Thus the specialized-transport and final-assembly placeholders
are bypassed, with no new intermediate statements or holes.

Repaired the performance defect in `ProjectiveDiagonalPullback`: `pullSectionIso`
keeps its original construction and signature, now marked `no_expose`, with the proved
characterizing theorem `pullSectionIso_eq`. The previous direct structure construction
exceeded 120 seconds; after this repair both proofs compile in 7.2 seconds in the full compatibility check.
Seven consumers require only removal of `pullSectionIso` from a local `irreducible`
attribute. Their signatures, imports and theorem bodies remain identical.

The two item nodes now record the actual proof dependencies. The definition node
records the new characterizing equation in its declaration list. The change record
is `coord/changes/N2-pull-section-iso-abstraction.md`.

## Proved and sorry left

Closed 2 of the item's 2 holes; added 0 holes; split off 0 statements:

- `AlgebraicGeometry.ProEtale.RationalP1.second_pull_section_core`
  (`lem-sfb-rational-p1-second-pull-section-core`).
- `AlgebraicGeometry.ProEtale.RationalP1.second_pull_section`
  (`lem-sfb-rational-p1-second-pull-section`).

Also proved the defining equation
`AlgebraicGeometry.ProEtale.RationalP1.pullSectionIso_eq` without any new axiom or hole.
There are zero holes in the item and its repaired definition module.
The unchanged holes in the consumer modules included solely for forced attribute
adaptation are:

- `AlgebraicGeometry.ProEtale.RationalP1.second_pull_section_core_comm`
  (`lem-sfb-rational-p1-second-pull-section-core-comm`).
- `AlgebraicGeometry.ProEtale.RationalP1.second_pull_section_final_assembly`
  (`lem-sfb-rational-p1-second-pull-section-final-assembly`). This is no longer imported
  by the item; its attribute still needs repair for whole-library compilation.
- `AlgebraicGeometry.ProEtale.RationalP1.canonical_section_projection_core_coherence`
  (`lem-sfb-projective-canonical-section-projection-core-coherence`).

The main proof still uses the already stated `second_pull_section_transport_data`
and `second_pull_comparison_inv_expansion` through their existing modules. Their
proof obligations are preserved, with no copy or restatement.

## No longer needed

Removed the item's proof imports of:

- `Sheaf.Paper.RationalP1SecondPullSectionTransportSpecialized`, node
  `lem-sfb-rational-p1-second-pull-section-specialized`: apply the already proved
  generic categorical transport directly to the concrete data.
- `Sheaf.Paper.RationalP1SecondPullSectionFinalTransport`, node
  `lem-sfb-rational-p1-second-pull-section-final-assembly`: the actual assembly is
  now the Lean proof of `second_pull_section`.

Only the final-transport module imports the specialized module, and the item was the
sole importer of final transport; both leave this proof's import closure. They are
retained in the library. All lower transport-data, inverse-expansion, core-equation
and generic-transport dependencies remain necessary. The unit's statement and proof
steps are preserved; the unit record has no realized steps bypassed by this change.

## Where the brief, the DAG or earlier work was wrong

The previous attempt correctly observed the slow kernel check, but local irreducibility
did not prevent imported kernel reduction of the exposed `pullSectionIso` composite.
Hiding that definition's body fixes the underlying performance issue while its exact
construction remains available by a proved equation. No compile limit was raised.

The docstring of `pull_section_transport` gives the stale node id
`lem-sfb-rational-p1-second-pull-section-transport`; its actual existing DAG node is
`lem-sfb-rational-pull-section-transport`, which the repaired proof node cites.

The specialized-transport and final-assembly placeholders were unnecessary: the generic
transport theorem already performs the required categorical calculation. The current
server queue row is a two-hole proof item, with no rework entry. Its recorded bad-import
build error is historical; the current dependency sources are available and compilation
uses the launcher overlay.

The required initial check of the retained packet printed an advisory that nothing was
proved but nevertheless pushed commit c6f67e3564e. This session continued the repair;
that no-op is not the proof delivery reported here.

## Forced adaptations

Each of the seven original consumer files was compiled against the changed definition.
Each failed with `failed to set reducibility status, pullSectionIso is not a definition`.
The following table gives the original error location. Each edit removes only that name
from the same local attribute line; no signature, visibility, proof or other attribute
changes. All 21 files in the compatibility set passed, including the repaired definition, all
ten direct importers, every module mentioning the changed name, and all seven adapted
consumers. Every file finished within 60 seconds (the slowest fresh check took 34.5
seconds). The item took 7.2 seconds with no warnings. Unchanged check copies were
removed after compilation; nine changed Lean modules remain in the delivery.

| Module | Original line | Holder checked on server |
| --- | --- | --- |
| `Sheaf.Paper.RationalP1SecondPullSectionCoreComm` | 27 | unclaimed |
| `Sheaf.Paper.RationalP1SecondPullSectionFinalTransport` | 27 | unclaimed |
| `Sheaf.Paper.CanonicalSectionProjectionCoreCoherence` | 28 | Y8 |
| `Sheaf.Paper.ProjectiveCanonicalSectionProjection` | 29 | unclaimed |
| `Sheaf.Paper.CanonicalSectionProjectionCore` | 29 | unclaimed |
| `Sheaf.Paper.CanonicalSectionProjectionTransport` | 27 | unclaimed |
| `Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor` | 243 | unclaimed |

## New nodes

None. The new proved characterizing equation belongs to the existing definition node
`def-sfb-projective-diagonal-pullback`; its Lean declaration list is updated.

## Forced adaptations

### Sheaf.Paper.CanonicalSectionProjectionCoreCoherence
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Related modules compiled before delivery

13 related module(s) compiled against this delivery by deliver3.py: 13 OK.

```json
{"capped": false, "direct": 11, "left_out": 0, "own": {"Sheaf.Paper.CanonicalSectionProjectionCore": "e47e5bced970419bfc14460a23f1a736766322c3", "Sheaf.Paper.CanonicalSectionProjectionCoreCoherence": "4fc622ddb9edb66500beb430a3e05bc018233a05", "Sheaf.Paper.CanonicalSectionProjectionTransport": "3cd0b52aaa994fd7ba80fcf58287cbdccae268d7", "Sheaf.Paper.ProjectiveCanonicalSectionProjection": "1c8141998dd11423cc788d2709fa79c6953d64c3", "Sheaf.Paper.ProjectiveDiagonalPullback": "da7b29ab46f92cc501b96211fd1df98420c58347", "Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor": "2491ac817143b1bdee9034d2173f87d3bae3aef2", "Sheaf.Paper.RationalP1SecondPullSection": "13e5e99df87c55e153ea18475d00218137c0ad91", "Sheaf.Paper.RationalP1SecondPullSectionCoreComm": "585294d174ee269dee3492951be1ec183d3495d7", "Sheaf.Paper.RationalP1SecondPullSectionFinalTransport": "c56ceb18b36fe5508f684053977725db0cff6fc2"}, "results": {"Sheaf.Paper.ProjectiveDiagonalComposition": {"hash": "4465c42b189a471e7b847b9725b82582010cbc11", "status": "OK"}, "Sheaf.Paper.ProjectiveNormalizedUnitCounitRestriction": {"hash": "89eb3a4c344c71dc1ade743614dee26b7358907b", "status": "OK"}, "Sheaf.Paper.ProjectiveSupportedSectionProjection": {"hash": "1f4e9827eddc9de852380fd0121d596fc2cea5e4", "status": "OK"}, "Sheaf.Paper.RationalP1AmbientComposites": {"hash": "108314f23b8ceb95f487cb8d52254a223d9c090d", "status": "OK"}, "Sheaf.Paper.RationalP1DiagonalTensor": {"hash": "dcf041758cf82f30421793f406ae664ef612f329", "status": "OK"}, "Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion": {"hash": "97902f0242b7f6dc2e0ca4ba5bcce432df6a3753", "status": "OK"}, "Sheaf.Paper.RationalP1SecondAmbientContraction": {"hash": "70744c2fdabe278f6c519afadda3c2519419dcf4", "status": "OK"}, "Sheaf.Paper.RationalP1SecondPullSectionTransportData": {"hash": "8752f783a6cb2a75fe90e14dc07ae0b0990ef620", "status": "OK"}, "Sheaf.Paper.RationalP1SecondPullSectionTransportSpecialized": {"hash": "dbae71dcf272c3e64801a9ac01bca2f122155288", "status": "OK"}, "Sheaf.Paper.RationalP1Triangle": {"hash": "d1e2d798a7453c8ae09756e0efc410fa7b065150", "status": "OK"}, "Sheaf.Paper.RationalP1UnitCounit": {"hash": "13d3d41003c57405f11cc6b1e7b75a523e27da5c", "status": "OK"}, "Sheaf.Paper.RationalTatePullback": {"hash": "9a6dcb60759ebb912f46ecdf84666017c639c8b1", "status": "OK"}, "Sheaf.Paper.TateTwistedProjection": {"hash": "7df3d71a566665354113bce4a2f1cfed5366afb6", "status": "OK"}}, "seconds": 139, "time": "2026-10-28T09:15:59+0800", "transitive": 2, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
