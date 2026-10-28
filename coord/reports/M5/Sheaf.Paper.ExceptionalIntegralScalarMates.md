## What changed

Constructed the finite reduction evaluation isomorphisms by composing the scalar
realization, `PurCompactSupport.finiteReductionIso`, and reconstruction evaluation,
then lifting through the full finite inclusion. Proved their ambient normalization.
The pointwise `exceptionalIntegralScalarMates_data_reduction_pointwise` now assembles
these explicit maps, the normalized left square, and a proved right square.

The right square is derived by transporting the actual system counit through the
reconstruction equivalences, evaluating it, and using injectivity of the finite
adjunction Hom equivalence. The generic conjugation and mate-uniqueness calculations
are fully proved private helpers. The left geometric normalization is isolated in
`Sheaf.Paper.ExceptionalIntegralReductionLeftCompatibility`.

Corrected `ReductionMates.evaluation_normalized` to include the canonical comparison
between the two derived quotient tensors. Relocated the existing data declarations
under the same names to `ExceptionalIntegralScalarMatesData`, publicly reexported by
the item, so the new left-square module has no import cycle. Details and all users:
`coord/changes/M5-exceptional-integral-reduction-normalization.md`.

Validation: all four packet modules and all six direct consumers compile without
warnings, each within the 60-second limit. The unchanged consumer copies were removed
after validation.

## Proved and sorry left

Closed the original hole
`WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_data_reduction_pointwise`
(node `lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise`). Added one
strictly smaller geometric left-square hole
`WeilConjectures.ExceptionalIntegralScalar.integralReductionLeftCompatibility`
(node `lem-sf-exceptional-integral-reduction-left-compatibility`). This is a decomposition:
one original hole closed, one lower hole added; there is no net decrease in holes.
The evaluation construction, normalization, right square and their combination are
complete Lean proofs and contain no sorry.

The two untouched holes in the item are
`WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_data_mates`
(node `lem-sf-exceptional-integral-scalar-mates-data-mates`) and
`WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_system`
(node `lem-sf-exceptional-integral-scalar-mates-system`). Thus the item contains two
sorries and the new left-square module one, three in the packet altogether.
No definition has a sorry and no arbitrary data is chosen from an unproved existence.

## No longer needed

The pointwise reduction proof does not need the existence theorem
`lem-sf-exceptional-integral-scalar-mates-data-mates`: its mate record is a parameter.
Its former direct proof dependencies `lem-sf-exceptional-system-transport` and
`lem-sf-exceptional-finite-scalar-mates` are replaced by the explicit evaluation and
left-square nodes, with the actual counit-conjugation tool cited directly.
The left-square step uses the reconstruction supplied in `transport`; it does not
call the reconstruction existence theorem `lem-sf-exceptional-integral-reconstruction`.
Adding that theorem as a fresh proof edge would introduce an indirect DAG cycle,
so the node correctly cites only the realization and normalized support comparison.
No whole existing module is withdrawn or globally pruned, and no unit route changes.

The following redundant direct public imports were removed from the item; every one
remains publicly reexported through its new data module:

- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`
- `Sheaf.Paper.ExceptionalSystemTransport`
- `Sheaf.Paper.ExceptionalFiniteScalarMates`
- `Sheaf.SixFunctors.IntegralSystemOperations`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.EtaleSystemCofinalMate`
- `Sheaf.Paper.CompletedScalarShiftCoordinates`
- `Sheaf.Paper.CoefficientExtensionReductionData`
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`

The data-only module does not import the item proof's four private dependencies:
`Sheaf.CategoryTheory.SystemSelectedAdjunctionIsos`,
`Sheaf.CategoryTheory.SystemSelectedNormalization`,
`Sheaf.Paper.RamifiedSystemRecoveryBounds`, and `Sheaf.Paper.FiniteCtfTriangulated`.
These remain private proof imports of the item where they are used.

## Where the brief, the DAG or earlier work was wrong

The finite normalization previously compared arrows built from two separately
recorded derived quotient functors by bare heterogeneous equality. The existing
`PurCompactSupport.finiteReductionIso` supplies an isomorphism, not literal equality
of those functors or their values. The repaired equation retains that canonical
comparison and transports the reconstruction endpoint equalities explicitly.
This is the same comparison used by the recorded compact-support identification.
The mathematical claim remains finite reduction compatibility with the chosen units.

The old pointwise plan did not distinguish construction of evaluation maps from the
left normalization and the formal right-adjoint consequence. Those steps are now
separate in Lean. At level zero the positive quotient exponent is still one, and the
categorical construction and cancellation arguments apply to empty categories as well;
no nonempty scheme, flat quotient, or faithful finite evaluation assumption was added.

## New nodes

`def-sf-exceptional-integral-scalar-transport-data` records the relocated data and the
explicit reconstruction evaluation realization in the new data module.
`lem-sf-exceptional-integral-reduction-evaluation` records the explicit finite evaluation
and its proved normalization. `lem-sf-exceptional-integral-reduction-left-compatibility`
records only the geometric left-square equation for these already constructed maps.
All retain the parent's chapter/unit and cite Zheng's reduction construction.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 3 OK.

```json
{"capped": false, "direct": 6, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalIntegralReductionEvaluation": "152cd9588b93436b53e2bd2db2492d2a93670ee5", "Sheaf.Paper.ExceptionalIntegralReductionLeftCompatibility": "873f04a25372fca520ec45e3562d1d5b0d4d3d0d", "Sheaf.Paper.ExceptionalIntegralScalarMates": "04ceff848d5669bc1e4fd85c2aee46b20aaea165", "Sheaf.Paper.ExceptionalIntegralScalarMatesData": "d1099be8012d930bcbf22e1396ab30fc4994c594"}, "results": {"Sheaf.Paper.ExceptionalRingOperationsExistence": {"hash": "12b6f37c3f38af79a030a433dc2ffb6b444cf31b", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreReconstruction": {"hash": "f4d71239a5c408af93197d8db822ef4effc14990", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "5960d42c061d3c3d87bda0f357d5137c36100426", "status": "INFRA"}, "Sheaf.Paper.ExceptionalTransportEndpointReconstruction": {"hash": "5596b992511530ac03b31e4507d88951cfd871c4", "status": "INFRA"}, "Sheaf.Paper.ExceptionalTransportLeftShift": {"hash": "c60bfd88a7f8711b3c8d88408449abf57ceeb426", "status": "INFRA"}}, "seconds": 152, "time": "2026-10-28T10:38:54+0800", "transitive": 0, "version": 1}
```

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
