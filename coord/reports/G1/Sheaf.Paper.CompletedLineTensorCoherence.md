## What changed

The naturality conjunct of `beta_natural_evaluation` is proved by expanding the
conjugated definition, applying naturality of the completion comparison and the
ordinary signed-line comparison, and cancelling the completion isomorphisms.
The independent evaluation conjunct is isolated as the named lower theorem
`beta_evaluation_compatibility`; the upper theorem combines it with the proved
naturality calculation. No existing declaration signature or definition was
changed. The public split theorem is documented in
`coord/changes/beta-evaluation-compatibility.md`.

## Proved and sorry left

The original `beta_natural_evaluation` hole was decomposed: its naturality
conjunct is closed, while the evaluation conjunct is represented by one strict
lower statement. The remaining sorry declarations are:

- `complete`
- `pairData_existsUnique`
- `beta_evaluation_compatibility` (new split-off statement)
- `scalar_coherence`
- `tower`
- `canonical_restriction`

No definition contains a sorry.

## No longer needed

None. The existing imports and DAG proof dependencies remain needed by the
module; the new evaluation statement is added to the twist/evaluation step.

## Where the brief, the DAG or earlier work was wrong

The planned evaluation step is substantially longer than the naturality step.
The naturality calculation can be completed directly from the existing
completion-comparison and ordinary-pair naturality equations, but the displayed
evaluation equation still requires the normalized ordinary evaluation argument.
No target statement was changed.

## New nodes

- `new-lem-pur-beta-evaluation-compatibility`, attached to
  `Sheaf.Paper.CompletedLineTensorCoherence`, declaration
  `WeilConjectures.CompletedLineTensor.beta_evaluation_compatibility`.

## Related modules compiled before delivery

29 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 28 OK.

```json
{"capped": false, "direct": 29, "left_out": 0, "own": {"Sheaf.Paper.CompletedLineTensorCoherence": "827053d04fb063f3cd0c806590e72c35f65e5a1c"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescent": {"hash": "6c7c25fb0eb44a4633534e59d0bfe31c66f7496e", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescentTower": {"hash": "05d7f1c1e7639986cebd67503ba00ab67ab3d425", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescentUnit": {"hash": "1bd7a8aabdf4843146cf1a902b75f4a3de8a57bd", "status": "OK"}, "Sheaf.Paper.CompletedScalarCanonicalAssociatorFormula": {"hash": "83977b558b3041c1ee0fedd59e4abb6c5dab8d8a", "status": "INFRA"}, "Sheaf.Paper.CompletedScalarTensorAssociatorCounit": {"hash": "3ad1ef741cc223fbbef33ced9ea0e67b062dae66", "status": "OK"}, "Sheaf.Paper.FdIntegralInverseScalarCocycle": {"hash": "8c1a916c018a491799e544a9eab67b99c6edc628", "status": "OK"}, "Sheaf.Paper.IntegralLineTensorCompleteness": {"hash": "d0e5300b279bf3f5ef1f7e289b1f63350bdf144b", "status": "OK"}, "Sheaf.Paper.IntegralScalarOrdinaryModelCoherence": {"hash": "7b3c710a0e8a2e97733cbb7d762155202db048ed", "status": "OK"}, "Sheaf.Paper.IntegralTwistAmbientCoherence": {"hash": "707f89bf50920f133ce82dcfaa5248f259428cf8", "status": "OK"}, "Sheaf.Paper.IntegralTwistCommonScalarModel": {"hash": "5393527d68326db602f60701e018943b2df79db8", "status": "OK"}, "Sheaf.Paper.IntegralTwistScalarCoherence": {"hash": "27a37c47d2fe79972e93548b1dcdf1d8b191385f", "status": "OK"}, "Sheaf.Paper.MixedReductionUnitComposition": {"hash": "00251a890dcb545bd55ad165b0d53c78506f1f41", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralScalarUnitUnderlyingBridge": {"hash": "c51a88f44d30e433b3bf18d0ab7e93087b2b4ad7", "status": "OK"}, "Sheaf.Paper.PerfectDualPairAndTateStability": {"hash": "9497eddbefc9d4bd78eb4a3f056ac54b281ae29d", "status": "OK"}, "Sheaf.Paper.PointEvaluationCompletionModels": {"hash": "97da6c35447defbb650c84625154d6981e405009", "status": "OK"}, "Sheaf.Paper.PointSectionsCompletionCone": {"hash": "97562935f210f54382513687d9ee98febf55a092", "status": "OK"}, "Sheaf.Paper.PurShiftedTateUnitScalarCoherence": {"hash": "60ef3239de34d437591ca5be666808ff99eb11cd", "status": "OK"}, "Sheaf.Paper.ScalarCompletionAssociator": {"hash": "339c04e954d10c42b8d70b5e2aa957aeab0edc91", "status": "OK"}, "Sheaf.Paper.ScalarShiftLineTowerTransport": {"hash": "dab59d6d3bc905afcfddeb9fd5f8c0bdd53caeea", "status": "OK"}, "Sheaf.Paper.TateTwistIntegralLines": {"hash": "b1adda22299e6bb70aaff4c1b4f341a5e21d024b", "status": "OK"}, "Sheaf.Paper.TateTwistLocallyFree": {"hash": "f65619f5d8b685a51cf53273ddfc9a673e670c5f", "status": "OK"}, "Sheaf.Paper.UnshiftedLineUnitTower": {"hash": "4aee908e6413e0fb311966d9fa4fdee94d5a8dbc", "status": "OK"}, "Sheaf.Paper.WfTateTwistCompatibility": {"hash": "ec4f543165caf27249e0881cf8d21dc305ec5dcb", "status": "OK"}, "Sheaf.TraceFormula.CounitRealizationSubstitution": {"hash": "ee657b489f6cef18cf2ce089aac7de9c1a67af9c", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelAssociativity": {"hash": "0f4a73b08c167cb3b8d31051f888cabe480781bd", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation": {"hash": "edccf15e40d131d4fbcc82664a0a4de25976a106", "status": "OK"}, "Sheaf.TraceFormula.ScalarModelUnit": {"hash": "f89e51f389a0416824798292d71e864addb838d4", "status": "OK"}, "Sheaf.TraceFormula.ScalarTensorRoosCoordinates": {"hash": "43ac44faf49790ce470786eaa6c67048e0c44c1a", "status": "OK"}}, "seconds": 135, "time": "2026-10-28T08:55:19+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
