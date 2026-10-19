# Strict-tower finite comparison selection

The H2 delivery timeout was caused by the representation of the normalization
predicate used by `StrictTowerProperOpenCalculus.finiteGamma`.
`Etale.properOpenInterchangeCoherence` returned two comparison families followed by
an inline conjunction of eight normalization/coherence clauses. Applying the
generic `secondWitness` helper to this theorem put the whole expanded conjunction
into the selected comparison's term. Profiling the current library module showed
22.4 seconds in one kernel type check, 22 seconds in module linting, and 16.2
seconds in serialization, before the additional retained proof work.

## Change

- Name the identical conjunction `Etale.properOpenInterchangeConditions` in
  `ProperOpenInterchangeCoherence.lean` and use it in the existing existential
  theorem. The theorem's proof body is byte-for-byte unchanged. Its type expands
  to the original type; no hypothesis or conclusion has changed.
- Mark `StrictTowerProperOpenCalculus.finiteGamma` `@[no_expose]` and provide
  `finiteGamma_eq_secondWitness`, the exact defining equation. The selected
  normalized comparison remains the same nested choice.

The generic `secondWitness` remains available with its original signature.
Consumers of `properOpenInterchangeCoherence` still obtain the same pair and
conditions; consumers of `finiteGamma` use the named comparison or its equation.
No mathematical hole is closed or added by this maintenance change.
The complete original (unfactored) theorem statement was checked in a Lean probe
by assigning `properOpenInterchangeCoherence Λ` to it, with no rewriting or
additional hypothesis. That probe compiled in 42.5 seconds.

All changed source files have `.bak` copies. The final coherence module compiled in 59.0 seconds and the calculus in 26.6
seconds. Validation results and the commit are recorded in the maintenance REPORT.md. All Lean checks use
`tools/lean_file.sh`, one file at a time, with the default 60-second limit.
No launcher tool, compile limit, admission policy, or dispatcher state is changed.
