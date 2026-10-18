## What changed

Proved `AlgebraicGeometry.Etale.derivedSquareIsoPasting` without changing its statement,
universes, hypotheses, or visibility. Six fully proved private helpers express the
comparison along an arbitrary diagonal, rearrange derived associativity in two ways,
and establish the identity and two pasting formulas for generic Grothendieck abelian
coefficients. The public theorem specializes these formulas to abelian groups and
cancels the source comparison isomorphisms.

The shorter route uses `pullbackSquareComparison_eq`,
`upperStarCompDerivedPlus_assoc`, and `upperStarCompDerivedPlus_id_left/right`.
It directly proves the equations on D-plus, so no new localization descent or
restriction proof is needed. The existing sheaf-level proof in
`WeilConjectures.SixFunctors.BaseChange.Pasting` supplies the algebraic pattern;
its generic `comp_inv_eq_inv_comp_of_eq` is used for the two rearrangements.
Added the proof-only import of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc` and retained both
original public imports. Updated the original DAG node's proof, proof dependencies,
and proof origin to describe this route. No definitions or public interfaces changed. The static classifier nevertheless
requires a change record for the additional scoped variable commands:
`coord/changes/X2-derived-square-pasting-private-context.md`. The record explains
that the context ends before the unchanged public theorem and no consumer adapts.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.derivedSquareIsoPasting`
(node `lem-weil-pbc-derived-square-iso-pasting`).
Added 0 holes; split off 0 obligations. There are no sorries left in the delivered
Lean module. Every private helper is proved. This is a proof, not a decomposition.

Validation: the completed file compiled through `lcompile.py` without warnings.
The delivery dry run additionally checks all declarations and their axiom dependencies.
The generic proofs require only commutative squares, so specializing to the stated
Cartesian squares is valid. Identity arrows are covered by the two unit laws;
no nonzero-object or nonempty-category assumptions are used.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories` (retired re-export).
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.SixFunctors.BaseChange.Square`.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.

The unchanged public imports already supply the definitions occurring in the statement.
`ChosenCartesianSquare` is not used: the proof needs only `IsPullback.toCommSq` and
Mathlib's pasting operations, not a chosen fibre-product identification.

The following original proof dependencies are no longer separate steps of this proof:
`lem-weil-pbc-square-iso-pasting`, `def-weil-pbc-cartesian-square`,
`def-weil-pbc-derived-inverse-image`, `def-weil-abstract-derived-category`,
`lem-weil-pbc-localization-universal-property`, and `def-weil-pbc-derived-categories`.
Their definitions or results can still occur transitively in the already-proved
coherence APIs; this report does not claim that they disappear from every target's
import closure. The square-pasting laws on sheaves are not reapplied or reproved.
No blueprint unit statement or step is bypassed (`sk-def-exchange` does not realize
this internal lemma as a unit step). No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old five-step proof plan was mathematically sound, but repeated a localization
argument already embodied in the derived associativity and unit laws. The source's
existing `pullbackSquareComparison_eq` makes a direct coherence proof shorter.
No false statement, missing dependency, definition repair, or tool failure was found.
The first dry run requested a change record for the new scoped variable context;
that record is now included.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
