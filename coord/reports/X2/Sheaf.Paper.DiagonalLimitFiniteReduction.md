## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.diagonal_limit_finite_reduction`
by a complete Lean assembly proof, preserving its exact signature and public imports.
It privately imports two new comparison modules.

`DiagonalCompletedReductionRestriction` isolates construction of simultaneous
completed/constant quotient reductions and their natural comparison, including the
quotient-unit equation. It involves no inverse limit, integral input, endpoints or
lifted arrow. `DiagonalAdicEvaluationComparison` isolates the natural isomorphism
between finite reduction of the constant-coefficient total limit and evaluation of
the integral quotient tower, normalized against the actual projection. It involves
no completed coefficient category, supported/Tate endpoints or lifted arrow.

The main proof constructs each endpoint isomorphism by composing the scalar
comparison, finite reduction of the supplied endpoint isomorphism, and the adic
comparison. Naturality of the quotient units proves the two unit equations.
Naturality of both comparisons and functoriality carry the whole-limit arrow
identity to the finite square; cancellation of the target isomorphism gives the
requested equation. These are separate parts of the original argument, not a
renamed or repackaged endpoint existence-and-naturality assertion.

Both new modules compile separately (8.2 and 7.1 seconds). The final assigned module
compiles without warnings in 23.3 seconds through lcompile.py. No existing interface
or consumer was changed.

## Proved and sorry left

Closed the one original hole:
- `AlgebraicGeometry.ProEtale.diagonal_limit_finite_reduction`
  (`lem-sfb-diagonal-limit-finite-reduction`). Its body is complete.

Added two named holes, each in a separate module with a source, proof in words and
matching DAG node:
- `AlgebraicGeometry.ProEtale.diagonal_completed_reduction_restriction`
  (`lem-sfb-diagonal-completed-reduction-restriction`).
- `AlgebraicGeometry.ProEtale.diagonal_adic_evaluation_comparison`
  (`lem-sfb-diagonal-adic-evaluation-comparison`).

This is a decomposition: one hole closed and two added, not a net proof gain.
The completed theorem uses sorry through exactly these two comparison obligations.
No sorry occurs in a definition or in a partial proof.

## No longer needed

No existing imports or modules were removed. The original direct proof dependencies
`lem-sfb-diagonal-derived-reduction-exists`,
`lem-weil-pbc-constant-completion-equivalence` and
`lemma-weil-pbc-adic-completion-reduction` are now located in the relevant comparison
nodes' proof plans; they remain needed there. The item itself depends directly only
on the two new comparison statements. There is no claimed global pruning.

## Where the brief, the DAG or earlier work was wrong

No false statement or route error was found. The existing completion-reduction and
constant-completion declarations use different strict K-flat/coefficient models,
and do not directly supply comparisons for arbitrary supplied diagonal D, L and N.
The original DAG's transport step includes this missing bridge. The two new nodes
state it independently of the endpoint-specific assembly.

The comparisons retain natural transformations, rather than only objectwise
isomorphisms: endpoint quotient-unit equations alone would not justify the finite
map equality. The main proof does not cancel a quotient unit or infer equality of
arbitrary derived maps from levelwise equalities.

Edge cases checked in stating the comparisons: n=0 still means reduction modulo
ell, not modulo 1; the zero object and empty scheme give zero comparisons; no
nonzero or invertible assumption is made on the morphism f or its lift. Arbitrary
a,b,s,t are transported exactly as supplied. The prime hypothesis is retained for
both new statements. The unit's completion and finite-reduction route is unchanged.

## New nodes

`lem-sfb-diagonal-completed-reduction-restriction` records finite scalar restriction
and the simultaneous normalized quotient construction. Its statement is in
`lean/Sheaf/Paper/DiagonalCompletedReductionRestriction.lean`.

`lem-sfb-diagonal-adic-evaluation-comparison` records the projection-adjoint
comparison for constant-coefficient total limits. Its statement is in
`lean/Sheaf/Paper/DiagonalAdicEvaluationComparison.lean`.

The item's DAG proof and proof_deps now follow the Lean assembly. No change record
is required for an existing interface: all existing signatures, definitions,
attributes and public imports are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalAdicEvaluationComparison": "2fa8d2ca93cb4bddd12ae5255b51320a57f68abc", "Sheaf.Paper.DiagonalCompletedReductionRestriction": "3ba846006efa83704fc3b9661478d45b6a6b99fa", "Sheaf.Paper.DiagonalLimitFiniteReduction": "5ca1082bfbd8a5a26eca17d49dc8238abfd64e0d"}, "results": {}, "time": "2026-10-28T12:07:16+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
