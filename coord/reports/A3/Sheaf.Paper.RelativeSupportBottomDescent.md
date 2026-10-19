## What changed

Closed ten existing proof holes in `Sheaf.Paper.RelativeSupportBottomDescent`: kernel additivity, the support-kernel injective preservation helper, global and evaluation acyclicity, terminal localization evaluation, restriction additivity and exactness, global derived isomorphism, kernel-forgetting naturality, and finite-colimit preservation of scalar forgetting. The public signatures and imports are unchanged.

## Proved and sorry left

Proved: `relativeSupportKernel_additive`, `relativeSupport_isAcyclic`, `relativeSupport_terminal`, `relativeSupport_evaluationAcyclic`, `relativeSupportRestriction_additive`, `relativeSupportRestriction_colimits`, `relativeSupportRestriction_limits`, `relativeSupportGlobalDerived_isIso`, `relativeSupportForgetIso_naturality`, and `relativeSupportModuleForget_colimits` (10 holes closed).

Six original holes remain, unchanged and named: `relativeSupportEvaluationIso_existsUnique`, `relativeSupportDerivedEvaluation_isIso`, `relativeSupportGlobalIso_existsUnique`, `relativeSupportForgetDerived_isIso`, `relativeSupportProComparison_isIso`, and `relative_support_bottom_descent`. No new `sorry` was added.

## No longer needed

No imports or DAG nodes were removed. The proof uses the existing support-kernel adjunction, étale lower-shriek exactness, kernel-preservation API, derived naturality, and ModuleCat colimit instances already imported by the module.

## Where the brief, the DAG or earlier work was wrong

No statement or DAG error was found. The remaining holes require the substantial geometric and comparison arguments recorded in the node; they were left as the original named theorems rather than introducing duplicate split statements.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
