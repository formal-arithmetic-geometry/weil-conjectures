# WeilConjectures.canonicalIntegralReductionTowerMap_naturality

## Reason

The delivery proposed a proof-only edit of this lemma in
Sheaf.Paper.IntegralReductionTowerCanonical. It said that importing the strict quotient
interfaces together with CompletionUnitModels fails, because two modules both lazily
generate `WeilConjectures.unrestrictedIntegralTransition.eq_1`.

The independent review (cc, 2026-10-26) withdrew the edit. The adaptation is not
forced: compiled against the published, unchanged IntegralReductionTowerCanonical, the
delivered modules Sheaf.TraceFormula.IsomorphismStrictQuotientModels,
Sheaf.Paper.CompletionUnitFixedCalculusModels,
Sheaf.TraceFormula.OrdinaryQuotientTowerComparison,
Sheaf.TraceFormula.StrictQuotientCompletionRealization and
Sheaf.TraceFormula.StrictQuotientCompletionUnit all compile with no duplicate-equation
error. The published library already has several importers of both modules. The
module therefore stays at its published version.

## Old

Unchanged (published version).

## New

Unchanged (published version). The proposed edit is withdrawn.

## Users

None. Nothing is changed.

## Status

withdrawn (reviewer, 2026-10-26)
