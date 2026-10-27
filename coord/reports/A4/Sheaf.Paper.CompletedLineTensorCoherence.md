## What changed

Proved `WeilConjectures.CompletedLineTensor.rational_diagonal` without changing
its statement. A private categorical lemma derives the diagonal identity from
the tower equation, naturality, and the actual scalar unit. The line hypothesis
verifies the tower compatibility by associativity of scalar action, using the
identity coefficient map. Cancel invertible beta and use faithfulness of the
identity scalar functor to obtain the normalized identity for every signed power.

Two proof-only imports supply fully proved extractions of the existing private
completeness-transport and scalar-localization-isomorphism arguments. Their old
private wrappers retain their signatures. Unit normalization uses a proved
private categorical conjugation lemma and a specific inverse-unit cancellation
law. These changes reduce the concrete proof elaboration in the long item file.
No existing public signature, definition body, exported attribute or public import
changes. Local irreducibility of `Padic` and local priority for `Algebra.toModule`
avoid expanding the p-adic construction during coefficient-instance synthesis.
These settings stay inside this file. No transparency relaxation is introduced. No other existing Lean module is
changed.

Validation: the item passes a fresh compile in 42.0 seconds with the final local
coefficient context. The two unchanged helper modules passed in 7.9 and 3.7
seconds, and the three-file set has been checked in import order.

## Proved and sorry left

Closed one of eight original holes:
`WeilConjectures.CompletedLineTensor.rational_diagonal`.
Added zero holes and split off zero obligations.

Seven original holes remain unchanged:

- `WeilConjectures.CompletedLineTensor.complete`
  (`lem-pur-signed-line-legacy-completeness`).
- `WeilConjectures.CompletedLineTensor.pairData_existsUnique`
- `WeilConjectures.CompletedLineTensor.associatorData_existsUnique`
- `WeilConjectures.CompletedLineTensor.beta_natural_evaluation`
- `WeilConjectures.CompletedLineTensor.scalar_coherence`
- `WeilConjectures.CompletedLineTensor.tower`
- `WeilConjectures.CompletedLineTensor.canonical_restriction`

The final six belong to `lem-pur-completed-line-tensor-coherence`.
This is a partial proof delivery. The new diagonal proof uses the existing tower
obligation through `rational_tower`; it does not claim to close that dependency.
Both new helper modules have zero holes.

## No longer needed

The diagonal case no longer needs a separate ordinary signed-power identity
calculation or transport through `rational_repeated`. The compatible tower and
the actual scalar unit force the identity. No module, node or import is withdrawn:
the other seven obligations retain their existing dependencies. The two added
imports are proof-only. All existing unit, evaluation and linearity helpers on
the current base are retained.

## Where the brief, the DAG or earlier work was wrong

The first delivery passed compilation and axiom probes, with eighteen importer
checks passing and one slow, then failed source availability: the shared snapshot
had temporarily shown an older ten-hole version without four inherited H1 helper
modules, while the server working tree still had the eight-hole version. The
shared snapshot now again matches the server. The final packet uses that current
eight-hole base and retains H1's evaluation and linearity proofs. No unavailable
helper file is restored or listed for deletion. The temporary rebase and duplicate
unit extraction are absent from this packet.

The recorded `IntegralLineTensorCompleteness` route cannot prove this module's
`complete`: that module imports this one and applies `complete` itself. This was
already noted in H1's earlier report. The completeness obligation is preserved.

The diagonal proof does not require reconstructing the ordinary diagonal square.
Its tower specialization plus the actual unit law supplies the result, including
zero and negative powers, without changing the statement.

## New nodes

`lem-pur-unrestricted-completeness-iso` records
`Sheaf.Paper.DerivedCompleteUnrestrictedIso`: the proved transport of the canonical
Roos witness along an isomorphism. It is the previous private `complete_of_iso`
argument, with the same independent scheme and coefficient universes.

`lem-pur-scalar-localization-component-iso` records
`Sheaf.CategoryTheory.ScalarLocalizationComponentIso`: the proved unique natural
isomorphism with specified raw-localization components. It is the previous
private `line_localizedIso` tensor-induction argument. It also handles zero rings;
the scalar function needs no extra properties.

Both are fully proved and add zero obligations. No existing definition or
interface changes, so no change record or consumer adaptation is needed.

## Related modules compiled before delivery

24 related module(s) compiled against this delivery by deliver3.py: 20 OK, 4 SLOW.

```json
{"capped": false, "direct": 24, "left_out": 0, "own": {"Sheaf.CategoryTheory.ScalarLocalizationComponentIso": "0042528dad8897483ca683e9a64bb74462454262", "Sheaf.Paper.CompletedLineTensorCoherence": "da5d3b09d9b6da7cc446da2c9578dd915975e358", "Sheaf.Paper.DerivedCompleteUnrestrictedIso": "2475ea0b3f2f1b9a1094324950e3037aac88ce4d"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescent": {"hash": "2711a1b70316e587b08b4f3187088cf8c66e0723", "status": "OK"}, "Sheaf.Paper.FdIntegralInverseScalarCocycle": {"hash": "8c1a916c018a491799e544a9eab67b99c6edc628", "status": "OK"}, "Sheaf.Paper.IntegralLineTensorCompleteness": {"hash": "d0e5300b279bf3f5ef1f7e289b1f63350bdf144b", "status": "OK"}, "Sheaf.Paper.IntegralScalarOrdinaryModelCoherence": {"hash": "7b3c710a0e8a2e97733cbb7d762155202db048ed", "status": "SLOW"}, "Sheaf.Paper.IntegralTwistAmbientCoherence": {"hash": "707f89bf50920f133ce82dcfaa5248f259428cf8", "status": "OK"}, "Sheaf.Paper.IntegralTwistCommonScalarModel": {"hash": "5393527d68326db602f60701e018943b2df79db8", "status": "OK"}, "Sheaf.Paper.IntegralTwistScalarCoherence": {"hash": "27a37c47d2fe79972e93548b1dcdf1d8b191385f", "status": "SLOW"}, "Sheaf.Paper.MixedReductionUnitComposition": {"hash": "00251a890dcb545bd55ad165b0d53c78506f1f41", "status": "OK"}, "Sheaf.Paper.PerfectDualPairAndTateStability": {"hash": "9497eddbefc9d4bd78eb4a3f056ac54b281ae29d", "status": "OK"}, "Sheaf.Paper.PointEvaluationCompletionModels": {"hash": "97da6c35447defbb650c84625154d6981e405009", "status": "SLOW"}, "Sheaf.Paper.PointSectionsCompletionCone": {"hash": "97562935f210f54382513687d9ee98febf55a092", "status": "OK"}, "Sheaf.Paper.PurShiftedTateUnitScalarCoherence": {"hash": "60ef3239de34d437591ca5be666808ff99eb11cd", "status": "OK"}, "Sheaf.Paper.ScalarCompletionAssociator": {"hash": "339c04e954d10c42b8d70b5e2aa957aeab0edc91", "status": "SLOW"}, "Sheaf.Paper.ScalarShiftLineTowerTransport": {"hash": "dab59d6d3bc905afcfddeb9fd5f8c0bdd53caeea", "status": "OK"}, "Sheaf.Paper.TateTwistIntegralLines": {"hash": "b1adda22299e6bb70aaff4c1b4f341a5e21d024b", "status": "OK"}, "Sheaf.Paper.TateTwistLocallyFree": {"hash": "f65619f5d8b685a51cf53273ddfc9a673e670c5f", "status": "OK"}, "Sheaf.Paper.UnshiftedLineUnitTower": {"hash": "4aee908e6413e0fb311966d9fa4fdee94d5a8dbc", "status": "OK"}, "Sheaf.Paper.WfTateTwistCompatibility": {"hash": "ec4f543165caf27249e0881cf8d21dc305ec5dcb", "status": "OK"}, "Sheaf.TraceFormula.CounitRealizationSubstitution": {"hash": "ee657b489f6cef18cf2ce089aac7de9c1a67af9c", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelAssociativity": {"hash": "58345451386edf9a165dff31c8e83d443441499c", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation": {"hash": "339922b4f1d7668d8e1aa9e1e72750669c14a3d6", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelUnit": {"hash": "db2903e7dc795254ef6a09f532f9ad903b6745f9", "status": "OK"}, "Sheaf.TraceFormula.ScalarTensorRoosCoordinates": {"hash": "43ac44faf49790ce470786eaa6c67048e0c44c1a", "status": "OK"}}, "seconds": 291, "time": "2026-10-28T00:54:55+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
