## What changed

Proved eight auxiliary theorems in `Sheaf.Paper.PurTwistSheafLocallyFree` without changing
any existing statement, definition, visibility or import. Added two proved private helpers:
`purTwistZlReduction_epi` and `purTwistZlFiniteFactor_ext`. The latter compares finite
factorizations at a common larger index by cancellation of the surjective p-adic residue map.

The constant-to-completed maps are constructed by the universal property of their actual
inverse limits. The completed scalar map factors the valuation-ring residue map through
`ZMod (l ^ (n + 1))`: since `l` lies in the maximal ideal, its `(n + 1)`st power lies in the
corresponding uniformizer-power ideal. These factorizations form a compatible cone. Finite
factorization extensionality proves uniqueness, including when two candidates use different
indices. Applying the finite projections proves the coefficient square. The two restriction
lemmas are the restriction clauses of the existing unique-action specifications.

The retained module compiled through `lcompile.py` in 7.2 seconds on 2026-10-19.
After restoring the eight proof-dependency imports added to the current library source
since the earlier attempt, the complete module compiled again in 8.8 seconds. The retained
proofs were checked against the current source: existing statements, definitions,
visibility and imports are unchanged in the delivery.
This is a partial proof delivery; the three larger original obligations remain unchanged.

## Proved and sorry left

Closed 8 of the original 11 holes, all under `AlgebraicGeometry.Scheme`:

- `AlgebraicGeometry.Scheme.purTwistZlCompletionMap_existsUnique`.
- `AlgebraicGeometry.Scheme.purTwistForgetPreservesSheafification`.
- `AlgebraicGeometry.Scheme.purTwistZlAction_restriction`.
- `AlgebraicGeometry.Scheme.purTwistIntegersMap_existsUnique`.
- `AlgebraicGeometry.Scheme.purTwistIntegralCompletionMap_existsUnique`.
- `AlgebraicGeometry.Scheme.purTwistCompletedScalarMap_existsUnique`.
- `AlgebraicGeometry.Scheme.purTwistCoefficientSquare`.
- `AlgebraicGeometry.Scheme.purTwistIntegralAction_restriction`.

Added 0 holes and split off 0 statements. Exactly 3 `sorry`s remain, all original named
public theorems attached to node `lem-pur-twist-sheaf-locally-free`:

- `AlgebraicGeometry.Scheme.purTwistZlAction_existsUnique`: construct the coordinatewise
  module structure on the actual root limit, prove compatibility with the power maps and
  restrictions, and use joint injectivity of the limit projections for uniqueness.
- `AlgebraicGeometry.Scheme.purTwistIntegralAction_existsUnique`: construct the completed
  action on the sheafified tensor and prove its pure-tensor normalization and uniqueness.
- `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free`: the finite and integral local
  trivializations, finite-basis coefficient comparison, finite reductions, constructibility
  and derived-completeness clauses of the original eleven-step argument remain to prove.

The two private helpers are proved completely. No definition contains `sorry`.

## No longer needed

None. No imports, nodes or modules are pruned in this partial delivery: the dependency
imports still describe the unchanged remaining main argument. The new proofs use the
existing imports and Mathlib's limit, ring-quotient and local-bijectivity APIs.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. For the auxiliary completed scalar map, the maximal
ideal containment alone permits choosing source index `k = n`; its construction does not
need to compute a ramification exponent. The finite-basis/cofinality argument in the main
node is still required and is unchanged. The main node's planned route and dependencies
remain in place for the three unproved declarations.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
