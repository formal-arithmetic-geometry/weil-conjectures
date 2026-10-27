## What changed

Added the component-level identity refinement theorem `systemRefinement_id_component` as a strictly simpler split-off statement. The existing `systemRefinement_id` theorem is proved from it by natural-transformation extensionality. The remaining three proof holes are unchanged.

## Proved and sorry left

Closed `WeilConjectures.CompactSupportCondensedRealization.systemRefinement_id` by reducing it to the component theorem. Added the named split-off theorem `systemRefinement_id_component`, whose proof remains `sorry` and is recorded by node `lem-pur-compact-support-condensed-realization-system-refinement-id-component`. Existing `systemRefinement_comp`, `omegaRefinement_isIso`, and `compactSupport_condensedRealization` remain `sorry`.

## No longer needed

None. The component proof uses the semilinear proper/open mate identity dependency.

## Where the brief, the DAG or earlier work was wrong

The original monolithic identity refinement hole hides a component calculation. Splitting that calculation into a theorem on one system object gives a strictly smaller proof obligation while preserving the original statement unchanged.

## New nodes

`lem-pur-compact-support-condensed-realization-system-refinement-id-component` records the component identity calculation and its source in the semilinear proper/open mate identity theorem.

## Related modules compiled before delivery

19 related module(s) compiled against this delivery by deliver3.py: 19 OK.

```json
{"capped": false, "direct": 19, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportCondensedRealization": "54f31cbb24083225a981b8dcae631ab42a617e74"}, "results": {"Sheaf.Paper.CompactSupportRealizationCoordinates": {"hash": "fccef3e9fbd21b120d003aed7419ff8000e7be40", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorNormalization": {"hash": "21a1fae00a5f5e376cdaca1227b75267f4c85edf", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorization": {"hash": "f227ba1ecb344881322e4822cdd8a9f7bad73a67", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealization": {"hash": "bf5692789db5a0ae189806d117c0b44ae7f79cfc", "status": "OK"}, "Sheaf.Paper.CondensedExceptionalReconstructionData": {"hash": "fdebf090817919002878b9f558bbbb7739915132", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitComparisons": {"hash": "d15a0f84ad12ce316c6c1d36de6f3af07d8f56d8", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitRealization": {"hash": "9e3a6c787b08bbc0f3c47e0278ed4e54bfa32abe", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.ExceptionalRealizationNormalization": {"hash": "895566ada038d17772c8ec83c407fc0ecb8cd54d", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionComparison": {"hash": "d2808d06efb721bf1bf12ac544724e77a081cd54", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionContext": {"hash": "65c9f8438b968b80d5fe5810cfd41538f8456aac", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionPresentations": {"hash": "073a85043c7885ad3aa0f40bb76f560f0d1e8c63", "status": "OK"}, "Sheaf.Paper.FilteredCondensedRepresentingPairData": {"hash": "46c3e859a82847b863ea8500c65cadbd8e2754fc", "status": "OK"}, "Sheaf.Paper.GeneralCondensedWeilRealization": {"hash": "77e3708cbf80f1fcbe19fc4478666b4b6faeac8d", "status": "OK"}, "Sheaf.Paper.MixedCupRingedNormalization": {"hash": "0d0f1f9df9a6c6b1fd6ae64036465afd935fd163", "status": "OK"}, "Sheaf.Paper.NativeWeilScalarFrobeniusCounit": {"hash": "744aa481959f2b15900ab73a5dbb0a8c7018ac42", "status": "OK"}, "Sheaf.Paper.PurIntegralRepresentingPair": {"hash": "23dba7f89db6e6b102862ec3b949470582089706", "status": "OK"}, "Sheaf.Paper.PurIntegralSupportComparison": {"hash": "ee354342d2ad136216093dabd5338e47edcf068f", "status": "OK"}, "Sheaf.Paper.PurIntegralSupportComparisonData": {"hash": "b0e1982e4560daf79a1cce2d412084616fd1bfb4", "status": "OK"}}, "seconds": 213, "time": "2026-10-28T01:34:30+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
