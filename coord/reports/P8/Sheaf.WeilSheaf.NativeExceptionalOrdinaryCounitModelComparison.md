## What changed

Proved the body of `native_exceptional_ordinary_counit_model_comparison` without changing
its signature or public imports. Constructed the forgetful models by lifting native
forgetting through the fully faithful realization and its constructible essential image.
Composed native open/proper forgetting, geometric closure transport and the specified
coefficient-system comparison, then lifted the natural isomorphism through right whiskering.

Added `NativeExceptionalClosureCompactSupport`, with a complete proof of
`native_exceptional_closure_compact_support`. Its private helpers prove open transport by
adjoint conjugation, proper transport by total-derived composition, and arbitrary
compactification comparison from a common refinement and scalar realization.

Added `NativeExceptionalCompactSupportRealization`, isolating the remaining ordinary
coefficient-realization step for arbitrary specified source and target Realizations and
System. It has no Weil category, finite-field model or forgetful-model conclusion.
All imports added to the existing item are proof imports. No other existing Lean module,
public interface, target, definition, instance or attribute was changed.

Validation: `lcompile.py --all` compiled the three modules in import order, with no
errors or warnings: scalar statement 1.8 s, geometric comparison 9.1 s, and assigned
module 8.9 s. The original theorem signature and public imports match the shared source
verbatim. All DAG dependency IDs and recorded Lean signatures were checked.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit_model_comparison`.
Also proved the new geometric theorem
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_closure_compact_support`.

One new hole remains:
`WeilConjectures.LocallyFiniteAdicCompactSupport.system_compact_support_realization`,
node `lem-sf-native-exceptional-compact-support-realization`, in its own new module.
Its body is exactly `:= by sorry`; its docstring and node contain its source and proof plan.

This is a decomposition: one original hole closed, one strictly ordinary scalar-realization
hole added, net zero holes closed. The item and geometric module have zero local sorries.
No definition or private helper contains a sorry. The native model construction, source
closure transport, arbitrary compactification change and final categorical lifting are Lean
proofs, rather than transferred existential obligations.

## No longer needed

No original Lean import was removed. The item no longer uses the original proof-plan
reference `lem-sf-native-weil-scalar-frobenius-counit` or imports its module: the desired
comparison has no Frobenius or counit normalization clause. The remaining scalar lemma
compares ordinary compact-support functors for the specified system directly.

The original direct proof dependency `lem-sf-adic-qbar-constructible-realization` is no longer
needed to construct the models for a given R; their essential-image lifts use R itself.
Its existence theorem is still used in the new geometric module to compare arbitrary
compactifications. Neither of these existing modules is claimed globally pruned: other
parents and public interface dependencies remain. No node or module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old single composite proof step did not supply typed comparisons for changing the
algebraic closure, changing compactification, and using arbitrary supplied coefficient
systems. The existing locally_finite_adic_compact_support_realization theorem chooses its
own Realizations and a StageAction for a lifted CoefficientConstruction. It cannot directly
be specialized to the specified R and System of this item. Its lower scalar-mate and
localization arguments provide the route for the remaining generic scalar statement.

The closure comparison has been proved using the same-middle compactification with source
and target isomorphisms; no additional native proper-base-change assertion is assumed.
Empty schemes and zero inputs require no inhabitedness assumptions. Identity maps and
identity coefficient transitions use the unit-normalized comparisons. The new scalar
statement assumes only the relative separated finite-type hypotheses; it does not add
absolute separatedness or choose different Realizations.

## New nodes

`lem-sf-native-exceptional-closure-compact-support`: geometric comparison of ordinary native
compact support under the specified closure transport. Proved, including arbitrary
compactification change using the remaining scalar comparison.

`lem-sf-native-exceptional-compact-support-realization`: ordinary native realization of an
arbitrary specified coefficient System, with specified source and target Realizations.
This is the single split-off scalar step. Its finite integral/rational normalization and
common-stage naturality are documented independently of the Weil-model problem.

No change record is required: only the assigned existing module and its own node are
changed; the two additional modules and nodes are new.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalClosureCompactSupport": "7d39293f80044355c3fead78b6479b741b5e65eb", "Sheaf.WeilSheaf.NativeExceptionalCompactSupportRealization": "0e1bed27eef4514e3b92a53d8c1baf6fa035934a", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitModelComparison": "b12486410164b5012881f5f5e168c95901430799"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison": {"hash": "654f73cd910ecc9a26a1f9c4d3656c79ee8d85d4", "status": "OK"}}, "seconds": 101, "time": "2026-10-28T10:35:31+0800", "transitive": 0, "version": 1}
```

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
