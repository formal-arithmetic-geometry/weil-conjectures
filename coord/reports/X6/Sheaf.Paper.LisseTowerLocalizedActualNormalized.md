## What changed

Repaired the false arbitrary-family statement in
`Sheaf.Paper.LisseTowerLocalizedActualNormalized`. The level isomorphisms in the
corrected theorem are explicitly the composites of a natural level comparison,
the inverse image of the supplied `e`, and the natural base comparison. Its Lean
proof combines the source coefficient square, naturality, `hδ`, and the target
coefficient square. A proved private categorical lemma performs this calculation
without unfolding the large sheaf constructions.

Adapted the sole caller, the unclaimed module
`Sheaf.Paper.LisseTowerLocalizedActual`, in the same delivery. Its statement is
verbatim unchanged. Its proof obtains one comparison system, constructs precisely
this family of level isomorphisms, and invokes the corrected theorem.

Added `Sheaf.Paper.LisseTowerLocalizationComparisons`. Its structure contains finite
inverse-image functors, natural level/base/scalar comparisons, and their two
independent coefficient squares. The source square has no level markings; the
target square concerns arbitrary semilinear arrows and has no etale model, adic
tower, markings or descent equation. The two operations on arbitrary semilinear
arrows are real constructions from the existing coefficient mate and restriction
compositor. No definition chooses a witness of an unproved existence theorem.

Change record: `coord/changes/lisse-tower-localized-actual-coherence.md`.

Validation: the new comparison module, repaired item and adapted parent compile
in import order, and the unchanged direct consumer
`Sheaf.Paper.LisseTowerLocalizedRealization` compiles against them (15.8 seconds).
The new module compiles in 12.7 seconds, the item in 11.6 seconds and the parent
in 9.0 seconds. The consumer test copy was removed from the delivery. The parent
signature was also checked byte-for-byte against the shared source.

## Proved and sorry left

The original item had one hole, in
`AlgebraicGeometry.Scheme.lisseTower_localized_actual_normalized`. Its original
statement is false, so this delivery does not count it as a proof of that
statement. The corrected constructed-family theorem has a complete Lean proof.
The parent `AlgebraicGeometry.Scheme.lisseTower_localized_actual` has a complete
proof of its original statement from the new geometric comparison lemma.

One hole is added and remains:
`AlgebraicGeometry.Scheme.lisseTower_localization_comparisons`, node
`lem-weil-pbc-lisse-tower-localization-comparisons`. Its proof is exactly `by sorry`,
with the construction and proof of both coefficient faces in its docstring and
DAG node. The new statement has no descended transition data or level markings;
it is the functorial inverse-image comparison step, not the old assertion about
arbitrary object isomorphisms under a new name. Naturality and application of the
supplied descent equation are proved in Lean in the item.

This is a statement repair and decomposition, not a claim that the original
geometric coefficient-cube obligation is now closed. Original holes proved: 0 of
1; holes added: 1. There are zero textual holes in the item and parent, and one
in the new module.

## No longer needed

Removed the private import `Sheaf.Paper.LisseTowerLocalizedActualLevels` from the
parent and removed `lem-weil-pbc-lisse-tower-localized-actual-levels` from its
proof route. Bare existence of unrelated level isomorphisms cannot prove their
coherence. The new natural comparison system both constructs the needed levels
and supplies the two independent coefficient faces, so the standalone level
existence result has no remaining Lean importer or DAG parent in the inspected
source. Its module and node were not modified or withdrawn: it is currently held
by X5. Its existing attachment and dependencies are preserved.

The original ring-sheaf coefficient mate, finite-projection compositor, and pulled
scalar comparison remain used through the new geometric node. They are not
claimed as globally pruned. The unit statement and the three unit proof steps in
`sk-thm-properbasechange` are unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original theorem universally quantified over `actual`
without any relation between `actual` and `e`. Naturality belongs to the functor
comparisons and does not hold for arbitrary object isomorphisms. For a geometric
point with coefficient ring F3 and zero ideal, the quotient levels from index 1
onward are F3. On the rank-one constant tower with identity transitions, changing
the sign of the level comparison at just one of levels 1 and 2 leaves
all hypotheses unchanged and would make the asserted equation identify -1 and 1.

The earlier split incorrectly combined bare level existence with this arbitrary-
family theorem. The repaired parent retains its existential conclusion, and its
DAG route now constructs a coherent family before applying the normalized result.
The statement correction records the original statement, all changed dependency
and proof fields, and the only citer. Its statement continues to hold unchanged.

The new comparison node uses the canonical pullback composition theorem as a
categorical tool (node
`lem-route-pro-etale-canonical-pullback-composition-exists-unique`), rather than
changing any unit route. Its ordinary inverse-image and sheafification sources
are Stacks Tags 03D2, 03D3 and 03CY; Tag 0D6D supplies composition. The old citations
to 03DA concern the abelian module category, not the full inverse-image composition
construction by themselves.

## New nodes

`lem-weil-pbc-lisse-tower-localization-comparisons` states existence of the functor
comparisons and their source and target coefficient squares. It is independent
of any chosen descended tower or its level markings, and the target face is
stated on an arbitrary semilinear arrow. Its small cases include zero modules,
zero rings and empty sites, where the same natural-transformation identities
apply. No boundedness, lisse, finite-cohomology, local marking or simultaneous
trivialization assumption is introduced. LeanSearch, Loogle, LeanFinder, Mathlib
text search, and project source search found the ordinary sheafification,
coefficient-mate and composition tools, but no existing declaration for this
concrete simultaneous cube. The node records those searches and the construction
step by step.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerLocalizationComparisons": "956f474c015a06a9e3eae2266b7fb71ab8e2b01a", "Sheaf.Paper.LisseTowerLocalizedActual": "413e8d6e26a48408c0cc86340d6cb8a1b61b41c3", "Sheaf.Paper.LisseTowerLocalizedActualNormalized": "4f1d8878afdc9f8947b4907c5ad699e088eeb6bb"}, "results": {"Sheaf.Paper.LisseTowerLocalizedRealization": {"hash": "7fc02abbc15c7911b37fc7c4d346153166d44694", "status": "OK"}}, "seconds": 110, "time": "2026-10-28T10:39:05+0800", "transitive": 0, "version": 1}
```

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
