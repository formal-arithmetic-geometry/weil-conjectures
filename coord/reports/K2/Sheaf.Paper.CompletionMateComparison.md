## What changed

Filled three existing theorem proofs in `Sheaf.Paper.CompletionMateComparison`.
`Site.deltaAdjunction_existsUnique` derives the normalized constant-tower adjunction
from the exact derived-adjunction construction. `Site.finiteAdjunction_existsUnique`
uses the finite scalar-extension/restriction adjunction and resolving-class
uniqueness. `Morphism.evaluatePushIso_existsUnique` constructs the normalized
isomorphism from the two universal right-derived units and localization.

The proof-only imports needed by these arguments are retained; no public statement
was changed. The tower-square definition now spells out the same pointwise
components to avoid repeated conversion through whiskering. See
`coord/changes/K2-completion-tower-square-explicit-components.md`.
Local irreducibility annotations keep the concrete
quotient-tower and pullback implementations abstract during elaboration.

## Proved and sorry left

Proved: `Site.deltaAdjunction_existsUnique`, `Site.finiteAdjunction_existsUnique`,
and `Morphism.evaluatePushIso_existsUnique` (3 of the 10 original holes).

All declarations below belong to `def-pur-adic-site-strict-quotient-interface`;
`completionMateComparison` also realizes `lem-sp-completion-mate-comparison`.

The original holes left unchanged are `moduleSquare_existsUnique`,
`Morphism.moduleReductionPullIso_existsUnique`, `Morphism.reductionPullIso_existsUnique`,
`Site.finiteEvaluationIso_existsUnique`, `Morphism.finitePullIso_existsUnique`,
`Morphism.finiteModuleRestrictionPullIso_existsUnique`, and
`completionMateComparison`. No new `sorry` declarations were added.

## No longer needed

No dependency modules or DAG nodes were pruned. The ordinary scalar-restriction
and finite-pullback probes were not integrated because their concrete conversion
still requires a separate interface proof.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is retained. The concrete derived-adjunction constructions require
reconstructing the local Abelian/Preadditive instances to avoid expensive instance
conversion; this is an elaboration requirement and does not alter any statement.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
