## What changed

Proved `AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts` in
`Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`, preserving its complete signature
and public imports. A uniform fibre-dimension bound gives d. Mathlib's
`IsAddTorsion.module_of_finite` and the existing torsion-sheaf characterization make every
underlying module sheaf torsion. Proper torsion vanishing and coefficient comparison give
module vanishing above 2*d; faithfulness reflects zero. The existing homology/single-object
comparison identifies this with classical higher images, so the finite-cd coproduct criterion
applies. The bounded-below comparison is the existing derived-functor compatibility iso.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`. Updated both existing nodes
attached to this declaration to record the actual proof and its dependencies. The current
main-20261015 blueprint route is retained: fibre bound, vanishing, finite acyclic-resolution
criterion. Its stalk and filtered-colimit arguments are carried by the two existing criteria.
No statement, definition, instance or visibility changed; no consumer adaptation is required.

Validation: the item is checked alone through `lcompile.py`; the delivery dry run performs the
standard compiler/probe and import checks. Edge cases require no exceptions: finite zero rings
are covered by Mathlib module torsion; empty fibres by the fibre-bound theorem; empty indexing
families and unbounded inputs by the unchanged finite-cd criterion. No nontrivial-ring,
constructibility, invertibility or boundedness assumptions were introduced.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts`
(nodes `lem-amb-proper-coproducts` and
`lem-etale-proper-derived-lower-star-coproducts-for-grothendieck`).

Item holes: 1 before, 0 after. Holes added: 0. Split-offs: 0.
There is no remaining `sorry` in any delivered Lean file. This is a proof from the stated
project dependencies; the existing proper-torsion-bound and finite-cd coproduct criterion
remain independent proof obligations in their own modules.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ProperBasic`: its theorem `AlgebraicGeometry.proper_basic` and
  node `pqf-lem-proper-basic` are unnecessary for this proof because Mathlib properness
  instances supply all geometric typeclass assumptions. Removed this node from the actual
  proof dependencies and its obsolete top-level tool-use entry where present.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`: the definition remains in use, but its wrapper
  import is redundant through the directly used upstream torsion-characterization module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: its direct-image definitions remain
  in use, but the explicit import is redundant through the retained public derived-coherence
  import.

No other node/module from the declared plan is pruned. In particular the proper torsion bound,
fibre-dimension bound, coefficient comparison, finite-cd coproduct criterion and plus
compatibility all remain used. No unit statement or realized proof step is bypassed; the
recorded unit `sk-prop-sf-cbc` has empty realized arrays.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. Searches used the launcher leanfinder, loogle and grep
services and source `rg`. The upstream theorem
`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` proves coproduct
preservation for an index in `Type (u + 1)`. The item quantifies over independent `Type w`;
the existing finite-dimension criterion has that exact universe-polymorphic conclusion,
so the delivered proof applies it directly rather than adding a universe conversion lemma. The old torsion step explicitly constructed an inverse to
the torsion-filtration colimit map; the existing proved torsion-sheaf characterization and
Mathlib finite-ring module torsion already provide the needed result. The DAG now records
that shorter implementation. The additional node attached to the same existing declaration
is updated consistently rather than stating a duplicate theorem.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
