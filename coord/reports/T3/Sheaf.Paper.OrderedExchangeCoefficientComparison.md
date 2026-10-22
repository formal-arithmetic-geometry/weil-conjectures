## What changed

Prove `rho_existsUnique` and `lambda_existsUnique` in
`Sheaf.Paper.OrderedExchangeCoefficientComparison`. Preserve every declaration signature
and all public imports. The two normalization predicates use equivalent presentations
that make their generic comparison proofs inexpensive to check. The change records are
`coord/changes/T3-rho-normalization-localization.md` and
`coord/changes/T3-lambda-normalization-factors.md`.

For rho, assemble the recorded completed reduction functor, its actual counit and its
properties as `DerivedReductionModelData`. Apply the existing `modelPull_existsUnique`
to those data, the target `reductionData` and `ordinaryRho.symm`. The existing flat-term
K-flat resolution supplies representatives; flat scalar restriction preserves the
required K-flatness. Scalar flatness follows from
`completed_constant_algebra_flat_quotients` after checking the coefficient projections.
`RhoNormalization` states that model comparison's complex-counit equation, with the
same K-flat and termwise-flat assumptions paired in a conjunction.

For lambda, identify the actual `limitComplexUnit` with `rightDerivedFunctorUnitQ`, use
preservation of K-injectives under termwise scalar restriction, and apply the existing
`towerComparison_existsLimitIso` to `ordinaryLambda`. `LambdaNormalization` retains its
equation before conjugating by the exact-restriction factorization isomorphisms; cancelling
these isomorphisms gives the old equation. On a K-injective representative, cancel the
invertible restriction factorization and source limit unit. Naturality transports
uniqueness to every derived object.

Add private proof imports and eight proved private helpers for scalar flatness and
K-flat restriction, the complex-level limit unit, categorical cancellation and transport
of component equality along an isomorphism. Update the existing DAG node's proof,
proof dependencies and proof origin. No other Lean module changes.

The final item compiled in 31.9 seconds, and all three unchanged direct importers
compiled against it (5.3, 7.2 and 26.2 seconds). The lambda normalization equivalence
compiled in 25.4 seconds. The generic rho presentation equivalence and its two concrete
counit identities compiled together in 53.9 seconds. The delivery tool performs the
remaining compile, axiom and preflight checks before pushing.

## Proved and sorry left

Closed 2 of the item's original 7 holes:

- `AlgebraicGeometry.Scheme.OrderedExchange.rho_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.lambda_existsUnique`.

Added 0 holes and split off 0 statements. The following 5 original named holes remain:

- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryRho_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.restriction_complete`.
- `AlgebraicGeometry.Scheme.OrderedExchange.phi_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.rho_unit`.
- `AlgebraicGeometry.Scheme.OrderedExchange.coefficientComparison`.

All seven declarations realize
`lem-weil-pbc-ordered-exchange-coefficient-comparison`. The rho proof still depends on
the original ordinary balancing hole. It proves the derived comparison from that existing
statement; it does not prove ordinary balancing.

## No longer needed

No existing imports, nodes or modules are withdrawn. The remaining obligations still
need the separated coefficient-comparison plan, so its dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The separated scalar-balancing, scalar-limit-square and completed scalar-adjunction
interfaces use the small pro-etale model with `SmallCategory`. This item uses the
original pro-etale site with different object and morphism universes. They are not
definitionally interchangeable. The two completed auxiliary proofs apply existing generic
derived comparison helpers directly to the original-site functors. Ordinary balancing,
completeness equivalence and the remaining unit and reconstruction compatibilities still
require site transport. No statement is disputed or weakened.

The old normalization presentations caused expensive concrete conversions of derived
localization maps. The change records give the old and new definitions, their equivalence
arguments, the declaration-user checks and the consumer checks. These definition changes
require the independent reader's review of the preserved target meanings.

The existing private helpers `modelPull_existsUnique`, `flatKFlatResolution`,
`exchangeTowerModuleRes_kinjective` and `towerComparison_existsLimitIso` are reused through
private proof imports. No copied or newly postponed version is introduced.

The additional direct proof dependencies are
`lem-weil-ringed-tower-pushforward-limit-comparison`, for its generic derived-limit helper;
`lem-weil-pbc-flat-scalar-restriction-kflat`, for K-flat restriction; and
`lem-weil-pbc-completed-constant-algebra-flat-quotients`, for scalar flatness. Their existing
declarations apply on the original site or to arbitrary abelian categories.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
