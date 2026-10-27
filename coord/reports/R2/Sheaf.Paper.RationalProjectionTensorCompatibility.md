## What changed

Restored the quarantined item module and retained its proved
`rationalProjectionTensorFunctorEq`, endpoint transport definitions, and canonical
tensor comparison. The original compatibility conjunction now combines two named
component statements: the compact-support square and the proper counit square.

## Proved and sorry left

`WeilConjectures.rationalProjectionTensorFunctorEq` remains proved, as do all
endpoint definitions and the final conjunction theorem, which is proved by pairing
the two component statements. Two strictly smaller local component statements are
split off and remain `sorry`:

- `WeilConjectures.rationalProjectionTensorCompatibility_compactSupport`, node
  `lem-sf-rational-projection-tensor-compatibility-compact`;
- `WeilConjectures.rationalProjectionTensorCompatibility_proper`, node
  `lem-sf-rational-projection-tensor-compatibility-proper`.

This closes the original conjunction hole by a genuine decomposition into its two
local mate calculations; the delivery leaves two named holes for parallel proof.
No definition contains `sorry`.

## No longer needed

The module has no proof-only imports beyond its existing public import. The final
proof route uses the shared tensor equality and the two new component nodes; the
unused direct proof dependencies from the earlier four-step sketch are not added
as direct dependencies of the parent route.

## Where the brief, the DAG or earlier work was wrong

The current structure supplies a per-exchange-square tensor comparison, while the
item constructs a separate canonical tensor comparison from the normalization
functor equality. No field identifies those two isomorphisms, so the full local
mate calculation cannot be discharged from the currently declared data alone.
The conjunction is therefore split into the compact-support and proper component
squares, each strictly simpler than the parent statement and retaining the
specified endpoint maps and hypotheses.

## New nodes

`lem-sf-rational-projection-tensor-compatibility-compact` records the compact-support
component square and is stated in the item module. `lem-sf-rational-projection-tensor-compatibility-proper`
records the proper counit component square and is stated in the item module. Their
proof obligations and source calculations are documented in the declarations.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SfP1ChartExchange

The original dependency proof compiled but emitted unused-simp-argument warnings
for `ordinaryFinitePullback`, `ordinaryFiniteLine`, and
`ordinaryFiniteDegreeZero` in its final `simp only` call. The delivery removes
only those three arguments; the theorem statement and all other proof lines are
unchanged. The adapted dependency and the item compile together.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SfP1ChartExchange
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
