## What changed

Proved `WeilConjectures.PurityFiniteSetting.augmentedFiniteRestriction_exact` by
forgetting to additive sheaves, where restriction is precomposition; reflection
transfers finite limits and finite colimits back to module sheaves. Additivity is
checked on sections.

Proved `WeilConjectures.PurityFiniteSetting.augmentedIntegralRoosDescent` from the
existing augmented reduction comparison and lower finite-clopen module gluing,
derived localization and countable-product results. The private
`integralRoosCalculus` first constructs the ordinary completed restriction
equivalence and descends it to derived categories. The proof then constructs the
projection-normalized product comparisons and the Hom bijection by fullness and
faithfulness. Naturality of the tower comparison identifies transitions;
its unit normalization identifies the actual first arrow of the Roos triangle.
A private product isomorphism and triangle-transport lemma keep these identities
explicit. No target, statement or definition is changed.
The private helper and the Roos proof locally exclude the overlapping generic
abelian and derived-category instances;
`coord/changes/T5-augmented-integral-local-instance-selection.md` records the
proof context and its empty consumer set.

Added proof imports of `ClopenStrictTowerRoosEquivalence`, `ProEtaleOperations`
and `DerivedCountableProductsExistence`; the tensor calculus import exposes its
existing private proof helpers. No upstream module is modified. The complete item compiles without warnings through
`lcompile.py` (55.1 seconds).

## Proved and sorry left

Closed two of the four original holes:

- `WeilConjectures.PurityFiniteSetting.augmentedFiniteRestriction_exact`.
- `WeilConjectures.PurityFiniteSetting.augmentedIntegralRoosDescent`.

Two existing holes remain, both attached to
`lem-pur-clopen-augmented-integral-descent`:

- `WeilConjectures.PurityFiniteSetting.augmentedIntegralReductionComparison`:
  the normalized chain, finite-derived and augmented-tower comparison.
- `WeilConjectures.PurityFiniteSetting.augmentedIntegralMembershipBounds`:
  completeness, constructibility and uniform cohomological/Tor bounds.

No holes added; no statements split off. All private helpers are proved.
The Roos theorem uses the existing reduction-comparison hole, as its original
proof plan requires.

## No longer needed

None. This is a partial implementation of the existing route; the remaining
reduction and membership statements still require their recorded dependencies.
No node, module or public import is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing module publicly imports its parent `ClopenRoosIntegralDescent` for
restriction definitions. The parent's unfinished results cannot be used to prove
this item's descent assertions without a mathematical dependency cycle. This
proof uses only the parent's restriction/coefficient helpers, together with the
lower gluing and Roos calculus. It does not invoke
`finiteClopen_derived_roos_descent`, `finiteClopen_augmented_reduction` or
`finiteClopen_integral_membership`.

The source has no current Lean importers, but its node is still required by its
unfinished parent. No withdrawal is proposed. The unit route is retained.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
