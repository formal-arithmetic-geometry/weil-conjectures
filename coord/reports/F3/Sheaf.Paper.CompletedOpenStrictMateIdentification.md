## What changed

Filled the proof of `AlgebraicGeometry.Scheme.completedOpenStrictMateIdentification`,
without changing its statement, endpoint definitions, public imports, or the existing
naturality theorem. The proof uses the declared finite-transpose coherence theorem,
then cancels the inverse strict square. A private categorical pasting lemma keeps the four
functors and their comparisons explicit. The proof transports that square to datum pullbacks,
applies limit functoriality and the scalar/open limit cube, and evaluates the specified
strict map using `completedRingStrictFiniteExchange`.

Added private proof imports of `CompletedOpenFiniteTransposeCoherence`,
`CompletedOpenStrictMateTranspose`, `CompletedOpenExchangeLimitNormalization`, and
`CompletedOpenScalarLimitSquare`. The latter module proves its scalar/limit square
from `UnboundedExactTower.constant_cube` and `exchangeMate_cube`, explicitly identifying
the project's named constant-diagram comparisons with these categorical constructions.
No adopted-source module, existing public definition, target, or other group's file
is changed. The completed parent compiled cleanly in 20.8 seconds through
`lcompile.py`. Its theorem signatures and original public imports were checked
verbatim against the dispatched source.

## Proved and sorry left

This is a decomposition, not a net proof of the original hole. One original hole is
closed: `AlgebraicGeometry.Scheme.completedOpenStrictMateIdentification`
(`lem-cbc-completed-open-strict-mate-identification`). Its three conjuncts have complete
Lean proofs from named declarations. The pre-existing naturality theorem is retained.

Two holes are added, both public theorems in separate new modules:

- `AlgebraicGeometry.Scheme.completedOpenStrictMateTranspose`, node
  `lem-cbc-completed-open-strict-mate-transpose`: identify the actual completed-ring
  inverse strict exchange's open-adjunction transpose with the published pulled unit.
  This concerns arbitrary K, before scalar restriction or inverse limit.
- `AlgebraicGeometry.Scheme.completedOpenExchangeLimitNormalization`, node
  `lem-cbc-completed-open-exchange-limit-normalization`: identify the chosen completed
  exchange with the limit of the simultaneous completed-ring strict exchange, after
  composing with the forward open/limit map. It contains no constant-scalar comparison
  or beta. Its source and full natural-language argument are in its docstring.

`AlgebraicGeometry.Scheme.completedOpenScalarLimitSquare`, node
`lem-cbc-completed-open-scalar-limit-square`, has a complete categorical proof and no
holes. The item's module has zero holes; the new modules together have two. Closing
one and adding two gives net -1 holes for this packet before transitive ledger effects.
Existing imported theorems with holes are not modified or counted as newly added holes.

## No longer needed

The proof does not use `Sheaf.Paper.CompletedOpenEndpointLimitTransport` or
`lem-cbc-completed-open-endpoint-limit-transport`; its endpoint definitions use the
chosen abstract open extension, while this item's definitions use `cbcOpenShriek`.
The formal scalar/limit cube is proved directly for the actual open functor instead.
That node is removed from this item's proof dependencies, not withdrawn globally.
No original import is removed; the endpoint module was a declared DAG dependency,
not a Lean import in the dispatched file. The strict proper/open calculus remains needed
for beta's definition, and finite-transpose coherence remains a proof dependency.
The explicit summand, K-flat and quotient calculations named in the old plan are
confined to the finite-transpose theorem and the new normalization lemmas; this
module does not separately import or reprove those calculations.

## Where the brief, the DAG or earlier work was wrong

The original plan's Steps 1 and 7 assumed normalization identifications stronger than
the currently stated declarations. `completedRingStrictFiniteExchange` gives a
representative equation and finite evaluation, not the open-unit transpose in the
actual tower adjunction. The completed exchange's unit equation does not itself state
its equality with Rlim of that same strict exchange. These two identifications are
now separate sourced statements, strictly parts of the argument. Their hypotheses
and conclusions are different from the parent scalar strict/limit/evaluation theorem.

The existing endpoint-limit transport theorem has separately chosen endpoint
functors and does not directly compare the `cbcRealization*` endpoints in the item.
No equality of morphisms is inferred from equality after derived evaluation. The
unit's prescribed finite-exchange then ordered-limit route is preserved.

## New nodes

`lem-cbc-completed-open-strict-mate-transpose` records the inverse strict exchange
normalization under the actual completed-ring open adjunction. Source: Stacks 03DI,
its explicit Hom correspondence, and strict derived descent of that formula.

`lem-cbc-completed-open-exchange-limit-normalization` records the completed-ring
limit normalization, using the completion universal property and the same finite
exchange. It is separate from the scalar/limit compatibility needed to combine it.

`lem-cbc-completed-open-scalar-limit-square` records the categorical constant-diagram
cube for the actual scalar/open comparisons. It is proved from the existing exact
localization cube and adjunction mate cube. All three nodes retain the parent's
chapter, unit and blueprint ancestry. The proof-context commands are recorded in
`coord/changes/F3-completed-open-mate-proof-context.md`; no existing statement or
definition changes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
