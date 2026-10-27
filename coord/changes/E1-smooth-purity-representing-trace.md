# AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace

## Reason

Implement the native representability-to-comparison and trace-transitivity-to-purity
parts of the declared geometric argument. This is partial proof work: the existing
trace definition and its three original theorem holes remain unchanged.

## Old

The complete item source is the archived
quarantine/WeilConjectures/SmoothPurity/Defs.lean. All its existing declaration signatures,
attributes, imports and definition bodies are retained verbatim. Its four holes were
smoothTrace, isIso_smoothPurityMap, smoothPurityIso_zero_of_isOpenImmersion and
smoothPurityIso_comp_openImmersion.

## New

Add six proved private theorems, with no new imports or public declarations:
smoothTrace_representingTranspose_isIso, smoothTrace_from_representing_pairing,
isIso_smoothPurityMap_of_representing_pairing, smoothTrace_conjugate_adjunct,
smoothPurityMap_comp_of_trace_transitivity and
smoothPurityIso_comp_of_trace_transitivity. Their full statements and proofs are
in the item module. Existing declaration texts and non-theorem bodies are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | E1 | Added proved private proof steps only. |
| Sheaf.Targets.SmoothPurityQbar | unchanged consumer | No public interface change. |
| WeilConjectures.PoincareDuality.Poincare | unchanged consumer | No public interface change. |
| WeilConjectures.TraceFormula.Dualizing | unchanged consumer | No public interface change. |
| TargetsCheck | unchanged consumer | No public interface change. |
| WeilConjectures | unchanged consumer | No public interface change. |

No downstream adaptation is required: no existing signatures, visibility, attributes,
instances, definitions or public imports change. No existing definition becomes
irreducible and no consumer is edited. No target changes its meaning.

## Status

landed 20261027T084349-L-3672956 2026-10-27 (merge of deliver/E1/WeilConjectures.SmoothPurity.Defs)
