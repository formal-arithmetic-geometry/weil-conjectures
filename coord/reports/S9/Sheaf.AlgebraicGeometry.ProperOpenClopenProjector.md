## What changed

Proved `clopenDerived_section_projector` in the assigned module. The proof descends
the existing termwise projector through unbounded localization, computes its open
restriction using the exact derived adjunction unit, and identifies it with the
specified intrinsic projector by adjunction uniqueness. Complementary vanishing
uses the exact composite functor and its compatibility with homology. Added a
private proof import of exact restriction composition and proved private helpers.
Public signatures and constructions are unchanged. The existing DAG records this
route; its final proper/open comparison step retains the original proof plan.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.StrictTower.clopenDerived_section_projector`.
Remaining original hole:
`AlgebraicGeometry.ProEtale.StrictTower.properOpen_clopen_projector`, with node
`lem-cbc-proper-open-clopen-projector` and its original source and proof docstring.
Holes closed: 1 of 2. Holes added: 0. Statements split off: 0.
The complete comparison attempt is retained only in the sandbox scratchpad.
The delivery tool records final compilation and preflight results.

## No longer needed

The completed descent does not use `lem-weil-pbc-exact-functor-derived-functor`
(`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`),
`lem-cbc-cochain-derived-adjunction`
(`Sheaf.Algebra.Homology.CochainDerivedAdjunction`), or
`lem-cbc-tower-adjunction-realization`
(`Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization`): the existing exact
tower operations and the `exactAdj_unit` and `exactAdj_jAdj` equations supply the
normalization directly. These were planned dependencies, not original imports.
Removed the obsolete exact-derived-functor tool approval from the node.
No module is withdrawn. The unfinished final step still retains
`lem-cbc-tower-open-beta-normalization`. The exploratory direct-image coherence
import is absent from this delivery because only the unfinished comparison used it.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The retained report claimed two closed holes
before a successful complete compile. This delivery instead reports the one
kernel-checked descent proof honestly. The full comparison attempt repeatedly
exceeded the file limit while normalizing specialized scheme pullback and derived
functor terms; this packet retains the original final theorem unchanged.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
