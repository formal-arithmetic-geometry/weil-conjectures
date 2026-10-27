## What changed

Filled all three theorem proofs in `lean/Sheaf/Paper/RationalTatePullback.lean`.
`coefficient_isCommMonObj` selects the existing instance in each coefficient case.
`linePull_existsUnique` transports the supplied signed sectionwise comparison across the
existing internal-module equivalences, preserving its exact adjunct equation, and proves
uniqueness by faithfulness and the adjunction Hom bijection. Its proof reuses the proved
private identity-on-sections pushforward bridge in `CartesianCoefficientTwists` through
`import all`, without changing that module. `residueIsUnit` maps a unit of the base field
along the structural residue-field homomorphism.

Added proof imports of `Mathlib.Algebra.CharP.Invertible`,
`Sheaf.Paper.CartesianCoefficientTwists` (all), and
`Sheaf.CategoryTheory.EquivalenceAdjunctionComparison`.
Recorded the argument and its actual dependencies in the existing node. No statement,
definition body, universe, public import, or source-library declaration was changed.
The unit route and the prescribed root/scalar/coprojection normalizations are preserved.

## Proved and sorry left

Closed 3 of 3 original holes, all under
`def-sfb-rational-tate-pullback-comparison`:

- `AlgebraicGeometry.ProEtale.RationalP1.coefficient_isCommMonObj`
- `AlgebraicGeometry.ProEtale.RationalP1.linePull_existsUnique`
- `AlgebraicGeometry.ProEtale.RationalP1.residueIsUnit`

No holes remain in the item. Added 0 holes; split off 0 statements.
The server compiled the complete file successfully (21.7 seconds). A second compile
with inline `#print axioms` (36.2 seconds) verified that each of the three proved
declarations uses only `propext`, `Classical.choice`, and `Quot.sound`. The diagnostic
commands were then removed.

## No longer needed

None. There were no planned proof dependencies to prune (the original node had an empty
proof plan). All added proof imports are used; the original public interface imports remain.
No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node supplied no numbered proof steps despite containing three postponed theorems.
The existing signed Cartesian comparison already supplies the degree-one isomorphism and
normalization needed for the linear lift; no new existence theorem or semilinearity
hypothesis is necessary. The generic equivalence comparison handles the transport.
No statement error was found. Small cases checked in the argument include both coefficient
indices, zero modules and empty schemes; no rank-one or nonempty hypothesis is used by the
linear-lift proof. The field argument uses precisely the two prime assumptions and p != ell.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
