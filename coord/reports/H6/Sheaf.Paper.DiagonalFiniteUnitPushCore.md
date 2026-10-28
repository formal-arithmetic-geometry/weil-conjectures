## What changed

Kept the statement and public imports of `Sheaf.Paper.DiagonalFiniteUnitPushCore`
unchanged. Added proof-only imports of `Sheaf.Paper.DiagonalFiniteConstantAdjunct` and
`Sheaf.Paper.DiagonalFiniteUnitTransport`.
The private, proved `realized_unit_one` calculation uses the actual coefficient-ring
units, both realization normalizations, naturality of the underlying-sheaf
isomorphism, and the ordinary push-square equation. The main proof evaluates
`singlePushComparison_square` at the regular module, transports the unit isomorphism
by naturality, and uses the full cochain equation `hcanonical` to identify the
canonical derived augmentation.
The proved generic helpers keep the calculation in abstract categories. The proved
`finite_push_unit_transport` API in `Sheaf.Paper.DiagonalFiniteUnitTransport` specializes
that algebra to arbitrary scheme morphisms. It is a new public theorem with zero holes.
`native_adjunct_in_model` handles the canonical-model conversion, and
`finite_unit_identity` cancels the original endpoint factor. Local irreducibility attributes keep
the concrete derived functors and coefficient comparisons closed during rewriting;
associativity is also proved in the generic helper. No shared
definition or attribute changes.

The remaining finite constant-adjunction calculation is stated in a new module.
It has only A, Y and an ordinary map m preserving coefficient one. It has no
condensed coefficient R, realization functors, arbitrary derived models, equality
of such models, or FinitePushSquare. Thus the delivery actually proves and removes
the realization and arbitrary-model parts of the argument; the new statement is
not the original square with its hypotheses renamed or bundled.

## Proved and sorry left

Original holes: 1. The body of
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finite_unit_push_square`
is complete from the new native finite constant-adjunction theorem.
The private `realized_unit_one` helper has a complete proof.
The private helpers `canonical_single_comparison`, `native_adjunct_in_model`,
`finite_unit_identity` and `transport_single_unit` also have complete proofs and no holes.
The new public `AlgebraicGeometry.ProEtale.DiagonalCoefficients.finite_push_unit_transport`,
node `lem-diagonal-finite-unit-transport`, is completely proved and adds zero holes.

Added holes: 1, exactly
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finite_constant_adjunct_of_one`,
in `Sheaf.Paper.DiagonalFiniteConstantAdjunct`, node
`lem-diagonal-finite-constant-adjunct`. Its docstring gives the source and complete
proof in words. The item itself has zero remaining holes. This is a decomposition
with one original hole discharged and one strictly lower hole added; the net hole
change is zero, not a completed proof of the whole dependency chain.

Validation: the final packet compiled in import order through `lcompile.py --all`,
with no compiler warnings. The new native statement took 9.1 seconds, the proved
transport module 56.5 seconds, and the item 50.1 seconds. All Lean lines are at
most 100 characters; the item statement and both original public imports are unchanged.
Profiling options and unused development imports have been removed.

## No longer needed

No existing imports, nodes or modules are pruned. All three original dependencies
remain necessary. No declaration or import in the adopted WeilConjectures tree is
changed. The new native statement needs no realization or arbitrary-model data;
those parts are now proved in this item rather than passed to its successor.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The old one-step proof plan
hid two different calculations: the normalization on coefficient one, and the
canonical finite constant-sheaf derived adjunct in the specified etale/pro-etale
coordinates. The delivery proves the former and all comparison-square transport;
the latter remains explicit in the new node. The existing proved generic
single-object square is used rather than recreated. Neither finiteness of A,
nonzeroness of A nor nonemptiness of Y is required. The zero-ring and empty-scheme
cases satisfy the new statement: the constant rank-one source is zero and the
unit equations and adjuncts are its unique maps. The blueprint unit route is kept.

## New nodes

`lem-diagonal-finite-constant-adjunct` states the native constant-sheaf
characterization of the finite unit adjunct by coefficient one. Its three steps
are constant rank-one extensionality, the proved single-right-derived counit
normalization and triangle identity, and compatibility of the canonical
constant comparisons with the specified finite pullback. Its Lean attachment is
`Sheaf.Paper.DiagonalFiniteConstantAdjunct.finite_constant_adjunct_of_one` in the
namespace `AlgebraicGeometry.ProEtale.DiagonalCoefficients`. No existing shared
interface changes and no change records or forced adaptations are needed.

`lem-diagonal-finite-unit-transport` records the proved transport API in
`Sheaf.Paper.DiagonalFiniteUnitTransport`. Its hypotheses separate the ordinary
factorization of a native map from its native derived-unit equation. Its proof
uses the existing single-object square and naturality, and is complete for any
scheme morphism. This node introduces no pending work.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalFiniteConstantAdjunct": "31f5dbdfac99d7dc2c6fc5e0b547ea22a68b2e4c", "Sheaf.Paper.DiagonalFiniteUnitPushCore": "485cf1b023cbf123b6ae9afb88c089b67d60b56f", "Sheaf.Paper.DiagonalFiniteUnitTransport": "f8560a415c7fd572bec0767cdedff7739ac0d298"}, "results": {"Sheaf.Paper.DiagonalFiniteUnitPush": {"hash": "eb8e124f6fb3e3046fea4786d72a79c1efe3dcb2", "status": "OK"}}, "seconds": 49, "time": "2026-10-28T11:37:05+0800", "transitive": 0, "version": 1}
```

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
