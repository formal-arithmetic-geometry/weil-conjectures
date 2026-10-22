## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientMate_diagonal_graph` by the four
steps of `lem-sfb-coefficient-mate-diagonal-graph`: the two pullback projections
identify the base-changed diagonal with the graph; the coefficient-mate composition
law gives the component equation; naturality at the diagonal and contravariant
functoriality give the section identity.

The six proved private helpers isolate the scheme projection calculation,
pushforward-composition components, presheaf naturality, evaluation on sections,
the diagram for three sheaves, and its application to a family of sheaves and mates.
The family formulation preserves the comma-category endpoint expressions used in
the public statement. It avoids expensive kernel comparisons that unfold the
concrete coefficient construction. No definitions or public signatures changed.

Added one private proof import,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`, for the
component formula of `lowerStarComp`. Existing public imports are unchanged.
The proof follows the existing DAG plan and dependencies; no node update is needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.coefficientMate_diagonal_graph`
(node `lem-sfb-coefficient-mate-diagonal-graph`), 1 of 1 original holes.
Added: none. Remaining in the module: none. Split off: none.
All six private helpers have complete proofs.

The complete proof passed `lcompile.py` in 5.2 seconds, including kernel checking.
The final delivery repeats compilation and performs the required preflight checks.

## No longer needed

None. All five declared proof dependencies are used. No public imports, nodes or
modules are removed, and the unit route is preserved. The existing composition
law and component formula suffice without new public statements or proof holes.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The inverse comparison occurs in the
geometric clause, and its forward component supplies the restriction on sections.
The argument applies to arbitrary sections and does not assume that `h` is a
monomorphism. Identity morphisms, empty test objects, and the zero ring require
no extra hypotheses or separate cases.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
