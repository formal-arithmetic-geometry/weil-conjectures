# Projection-formula coherence in the blueprint's direction

## Reason

Route audit 2026-10-25 (batch 5 #4), approved by the human 2026-10-26. In the blueprint
fix-prop-projection-formula USES prop-sf-pf-coherence; here `Sheaf.Paper.ProjectionFormulaCoherence`
cited `compactSupportProjectionFormula` (node fix-prop-projection-formula) five times.

## New

* `Sheaf.Paper.CompactSupportProjectionCoherenceLaws` (new): `compactSupportProjection_coherenceLaws`,
  the structural laws at every coefficient stage, assembled from the three stage-law lemmas
  (finite, integral, field). `compactSupportProjectionFormula` had exactly this statement and proof.
* `ProjectionFormulaCoherence` cites it and no longer imports `CompactSupportProjectionFormula`.
* DAG: prop-sf-pf-coherence cites the stage laws instead of fix-prop-projection-formula; five edges
  into fix-prop-projection-formula that neither the blueprint node nor the Lean declaration uses
  were repointed (def-pur-co-smoothness, lem-coef-finite-exceptional, lem-pur-coprojection,
  lem-sf-finite-adjunction-system-duality → lem-weil-finite-compact-projection-formula;
  lem-coef-dual-formula-scalar-transpose → lem-pur-compact-support-projection-coefficient-change);
  fix-prop-projection-formula now cites prop-sf-pf-coherence. No cycle.
