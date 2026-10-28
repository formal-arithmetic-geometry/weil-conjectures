## What changed

Restored the complete assigned source from its quarantine copy and proved
`WeilConjectures.CoefDualFormulaScalarTranspose.beta_isIso`. Its prescribed beta is
`v(K, omega_E)` followed by internal Hom applied to `(identity, u)`. The existing
`IntegralFiniteExtension.comparison_invertibility` theorem supplies invertibility
of both `v` and `u` for the arbitrary tensor presentations in this statement.
Functoriality and composition of isomorphisms finish the proof.

Added only the private proof import
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility`. Public imports,
declaration signatures, definition bodies, and existing docstrings are unchanged.
Updated the item's DAG proof, proof dependencies, and proof origin to record this
implemented step; no other existing module or node is adapted.

The assigned rework row records a failure of the dependency
`Sheaf.SixFunctors.IntegralNormalizedFamily`. That root was repaired independently
by A2 in the current shared source; its report describes the explicit conversion
of `DiagonalCompletedLimitSpec` to `DiagonalTrace.IsDiagonalLimit`. The archived
item's original import failure is preserved in its build-error record. The
unaltered assigned module compiled in 34 seconds against the published build
before this proof change. This delivery adds an actual proof rather than
claiming that a no-op rebase repairs the earlier root failure.

## Proved and sorry left

Closed 1 of the 5 original holes, with 0 new holes and 0 statements split off:

- `WeilConjectures.CoefDualFormulaScalarTranspose.beta_isIso`.

Four original named theorem holes remain unchanged, all attached to
`lem-coef-dual-formula-scalar-transpose`, with their existing source and proof
in words retained:

- `WeilConjectures.CoefDualFormulaScalarTranspose.trace_existsUnique`.
- `WeilConjectures.CoefDualFormulaScalarTranspose.pullCompletion_existsUnique`.
- `WeilConjectures.CoefDualFormulaScalarTranspose.formula_existsUnique`.
- `WeilConjectures.CoefDualFormulaScalarTranspose.coef_dual_formula_scalar_transpose`.

The new proof uses existing project theorems; it does not claim that all of their
transitive dependencies are free of sorry. Final compilation and the axiom probe
are performed by the delivery tool.

## No longer needed

No import, module, declaration, or DAG node is removed. The remaining four holes
retain their existing proof plans and dependencies. For `beta_isIso` alone the
full finite-level evaluation/presentation-independence argument is unnecessary:
the existing arbitrary-presentation invertibility theorem already supplies its
two factors. The unit route is unchanged and its `realized` fields are empty.

## Where the brief, the DAG or earlier work was wrong

The old G1 report correctly noted that the existential tensor presentations in
`coef_integral_finite_extension` could not directly prove the arbitrary supplied
presentation case. The newer `comparison_invertibility` declaration quantifies
over those presentations and resolves that exact gap. No presentation is changed
or selected by the proof. The identity extension, ramified extensions, zero
complexes, and empty schemes require no additional hypothesis: the argument is
composition and functorial transport of the existing canonical isomorphisms.

The rework record predates A2's root repair; no repair to that other module is
included here, and no quarantined declaration or attachment is withdrawn.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefDualFormulaScalarTranspose": "0f7df824dd97c32746df97be275b1933e9025c38"}, "results": {}, "time": "2026-10-28T09:40:05+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
