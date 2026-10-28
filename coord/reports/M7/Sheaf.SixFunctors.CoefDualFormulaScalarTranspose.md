## What changed

Proved `WeilConjectures.CoefDualFormulaScalarTranspose.pullCompletion_existsUnique`
in the assigned module. On good K-flat complexes, compose the existing ordinary
pullback factorization, the termwise adjunction-normalized `ordinaryPullIso`, and
the actual strict quotient/zero-coordinate completion chain map. The latter is
already a natural transformation. Fully faithful restriction along the existing
good-complex localization uniquely descends this comparison; its component
formula is exactly the required normalization.

Added two private proof imports, `import all
Sheaf.Paper.OrdinaryIntegralPullbackConstruction` and `import all
Sheaf.Paper.IntegralOperationsWellDefined`, to use their existing private chain
naturality and localization/descent helpers. No existing signature, public import,
definition body, or docstring changes. Updated only the assigned node's proof,
proof dependencies and proof origin. No other module or node is adapted.

## Proved and sorry left

Closed 1 of the 4 original holes:
`WeilConjectures.CoefDualFormulaScalarTranspose.pullCompletion_existsUnique`.
Added 0 holes; split off 0 statements.

Three original named theorem holes remain unchanged, each attached to
`lem-coef-dual-formula-scalar-transpose`, retaining its source and complete proof
in words:

- `WeilConjectures.CoefDualFormulaScalarTranspose.trace_existsUnique`.
- `WeilConjectures.CoefDualFormulaScalarTranspose.formula_existsUnique`.
- `WeilConjectures.CoefDualFormulaScalarTranspose.coef_dual_formula_scalar_transpose`.

The proof uses existing project theorems, so this does not assert that every
transitive dependency is free of sorry. Compilation and the delivery axiom probe
check the resulting module.

## No longer needed

No import, module, declaration, or node is removed. The three unchanged holes
retain their existing proof dependencies. For the completed-pullback comparison
alone, no finite-level exceptional or duality theorem, constructibility argument,
or invertibility of the completion map is needed: naturality of the strict chain
map and the good-complex localization suffice. The unit route is unchanged; its
`realized` statement and step lists are empty.

## Where the brief, the DAG or earlier work was wrong

The current server queue lists a stage-3 proof item with four holes. The preserved
build-error record lists failed imports of CoefIntegralFiniteExtension,
QcqsCompactSupportRealization, and ConstructibleExceptionalAdjunctionCoefficients.
These files are currently present on the server, and the unaltered assigned
module compiled in 36.6 seconds against the published build. This delivery closes
an actual existing hole rather than treating that old import report as a repair
accomplished by a no-op.

The existing ordinary integral pullback construction already supplies the strict
natural completion chain and generic normalized-comparison descent machinery.
They apply directly to the ringed pullback presentation through `ordinaryPullIso`;
no new intermediate mathematical statement is necessary. The proof is categorical
and uses no nonemptiness or nonzero-object hypothesis, so empty schemes, zero
complexes, and identity morphisms require no special cases. It retains the full
zero cone coordinate rather than claiming faithfulness of finite reductions.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefDualFormulaScalarTranspose": "98951bd54b02d09065c303bfb22910d683cd7fa4"}, "results": {}, "time": "2026-10-28T14:08:02+0800", "transitive": 0, "version": 1}
```

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
