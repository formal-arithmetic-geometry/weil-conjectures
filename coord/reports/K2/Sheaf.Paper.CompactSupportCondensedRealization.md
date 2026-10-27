## What changed

Added `GammaIdentityCondition`, the theorem supplying this condition from the generic semilinear mate identity, and the conditional identity-component calculation. Proved `systemRefinement_id_component` by applying those two strictly smaller declarations. Existing wrapper proofs for `systemRefinement_comp` and `omegaRefinement_isIso` remain unchanged; imports and target signatures are preserved.

## Proved and sorry left

Closed `systemRefinement_id_component`.

The following five declarations remain sorry: `gammaIdentityCondition_exists` (node `lem-pur-compact-support-condensed-realization-gamma-identity-condition`), `systemRefinement_id_component_of_gamma` (node `lem-pur-compact-support-condensed-realization-id-component-of-gamma`), `systemRefinement_comp_component` (node `lem-pur-compact-support-condensed-realization-system-refinement-comp-component`), `omegaRefinement_isIso_component` (node `lem-pur-compact-support-condensed-realization-omega-refinement-iso-component`), and `compactSupport_condensedRealization` (node `lem-pur-compact-support-condensed-realization`).

## No longer needed

None. All existing imports remain used by the module or its declared proof route.

## Where the brief, the DAG or earlier work was wrong

The generic `gamma_identities` theorem is stated for the semilinear derived presentation, while this module exposes the coefficient-sequence derived presentation; these are not definitionally equal under the module's transparency settings. The new condition isolates that presentation bridge and the mate-pasting calculation, so the component theorem can be proved without changing its statement.

## New nodes

`lem-pur-compact-support-condensed-realization-gamma-identity-condition` records the explicit identity equation used by the mate calculation. `lem-pur-compact-support-condensed-realization-id-component-of-gamma` records the categorical identity-component calculation under that condition. Both are in the item's module and are strictly below the existing component theorem.

## Related modules compiled before delivery

13 related module(s) compiled against this delivery by deliver3.py: 13 OK.

```json
{"capped": false, "direct": 13, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportCondensedRealization": "cc1a66f277773a79d8bbf10c18b7f4a69c05d265"}, "results": {"Sheaf.Paper.CompactSupportRealizationCoordinates": {"hash": "fccef3e9fbd21b120d003aed7419ff8000e7be40", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorNormalization": {"hash": "21a1fae00a5f5e376cdaca1227b75267f4c85edf", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorization": {"hash": "f227ba1ecb344881322e4822cdd8a9f7bad73a67", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationData": {"hash": "a0c7b3b8f4c75aba5a0683ba8ad1d550af600aee", "status": "OK"}, "Sheaf.Paper.CondensedExceptionalReconstructionData": {"hash": "fdebf090817919002878b9f558bbbb7739915132", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitComparisons": {"hash": "d15a0f84ad12ce316c6c1d36de6f3af07d8f56d8", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitRealization": {"hash": "9e3a6c787b08bbc0f3c47e0278ed4e54bfa32abe", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.ExceptionalRealizationNormalization": {"hash": "895566ada038d17772c8ec83c407fc0ecb8cd54d", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionComparison": {"hash": "d2808d06efb721bf1bf12ac544724e77a081cd54", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionContext": {"hash": "65c9f8438b968b80d5fe5810cfd41538f8456aac", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionPresentations": {"hash": "073a85043c7885ad3aa0f40bb76f560f0d1e8c63", "status": "OK"}, "Sheaf.Paper.FilteredCondensedRepresentingPairData": {"hash": "46c3e859a82847b863ea8500c65cadbd8e2754fc", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T05:57:12+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
