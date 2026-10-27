## What changed

Replaced the hole in `Sheaf.Paper.SfNormalizedRationalWeilSquares` by a complete
categorical assembly. The statement is unchanged. Three proved private helpers give:

- the closed square from the actual right mate and `unit_mateEquiv`;
- transport of that square through a natural isomorphism preserving the unit;
- the open square by rotating two distinguished triangles and completing their
  prescribed middle and closed isomorphisms to an isomorphism of triangles.

The proof uses the published `fieldWeilProperExchange` (not an arbitrary comparison),
`sfNormalizedRationalRecollement_triangle_orthogonality` for its triangle-existence
clause, and exactness of the specified Frobenius from
`automorphismConstructibleStage_integral_rational`. All added item imports are proof-only.

Added `Sheaf.Paper.SfNormalizedRationalClosedComparison`, containing one public theorem
which identifies the normalized closed term and unit with the actual proper adjunction.
This is the closed coefficient-normalization step of the old proof, with no Frobenius
structure, Weil-pair input, open square, or triangle assertion. It is strictly a part
of the old obligation; the mate and triangle arguments are implemented in the item.
The change record is `coord/changes/E5-normalized-rational-closed-comparison.md`.
Updated the item's proof, proof dependencies, proof origin and proof docstring to match.

## Proved and sorry left

One original textual hole is closed:
`WeilConjectures.sfNormalizedRationalRecollement_weil_squares`
(node `lem-sf-normalized-rational-recollement-weil-squares`). The item has zero sorries.
Its three private categorical helpers are completely proved.

One hole is added and remains:
`WeilConjectures.sfNormalizedRationalRecollement_closed_comparison`
(node `lem-sf-normalized-rational-closed-comparison`). Its entire proof is `by sorry`;
its docstring and node state its source and full proof in words. Thus this is a
**decomposition**, closing one hole and adding one strictly smaller hole, net zero;
it is not counted as a completed proof of the original mathematical obligation.
Existing imported holes are used as the brief permits; none is changed or restated.

Validation: the complete assembly compiled successfully with `lcompile.py`. The final
helper uses the compiler-suggested explicit simplification; delivery checks compile
the final packet and run its axiom probes.
No definitions, target signatures, source-library files, or existing public imports change.

## No longer needed

No existing import line was removed: the original item imported only its statement data.
No existing module is withdrawn, and no global module-pruning claim is made.

The item's former direct proof dependencies are replaced as follows:

- `lem-sf-open-closed-weil-mate-structures` / `Sheaf.SixFunctors.OpenClosedWeilMateStructures`
  is unnecessary for this proof. The already published proper exchange is its actual
  invertible right mate; Mathlib's unit equation proves the needed square directly.
  The separate open mate, open-complement geometry, and all common-stage mate clauses
  are unnecessary, because the open isomorphism follows from the localization triangle.
- `def-weil-frobenius-detailed`, `def-sf-recollement-presentation-data`, and
  `def-weil-rationalization-karoubi` remain used through the actual statement and
  imported interfaces, but require no separate direct proof-dependency entries for
  this assembly. The closed comparison node retains the rationalization dependency.

The old proof's explicit open-complement construction, open coefficient comparison,
and tensor calculation for the open Frobenius word are consequently not separate
obligations of this item. The unit's localization-sequence route is retained; its
`realized` lists are empty and no unit record changes.

## Where the brief, the DAG or earlier work was wrong

The old planned route was not false, but it prescribed more comparison work than the
conclusion needs. The triangle-existence theorem is independently proved and has no
Weil-square dependency, so its use here is not circular. Rotating those triangles
reduces construction of both outer structures to the closed structure alone.

The new comparison statement was checked against the empty closed subscheme, identity
closed immersion, zero object, and conjugation by the arbitrary normalization
isomorphisms allowed in P and Q. The unit equation, not merely an isomorphism of
objects, is essential: it is exactly what the conjugation helper consumes. Rational
naturality follows from the localization universal property (fractions of integral
arrows); it does not assume an unstated linearity of arbitrary Q.

Repository and Mathlib searches found no existing theorem stating the new comparison.
The general adjunction-uniqueness and localization-unit formulas were read; they handle
its categorical end, but not the actual completed-to-rational identification.
The blueprint search for normalized closed adjunction found only general operation
and adjunction nodes, not this normalized presentation comparison. The blueprint
ancestor script returned None because the original split records a module name as
`created.item`; the new node uses the original node's explicit blueprint ancestor.

## New nodes

`lem-sf-normalized-rational-closed-comparison` is the closed coefficient-normalization
step: identify the actual normalized rational closed functor and its unit with the
specified rational proper adjunction. It contains no Frobenius conclusion. Its Lean
module has one named theorem and one hole, three kinds of actual search plus LeanSearch,
the source, proof in words, and exact Lean statement. The associated change record is
`coord/changes/E5-normalized-rational-closed-comparison.md`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
