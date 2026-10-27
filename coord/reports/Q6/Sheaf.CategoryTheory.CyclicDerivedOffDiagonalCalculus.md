## What changed

The original theorem `cyclicDerivedOffDiagonal_calculus` is reduced, without changing
its statement, to two concrete calculations about the normalized free triangle.
The main proof applies contravariant representable exactness to the triangle and
its rotation, explicitly handles the rotation minus sign, and transports all three
exact pairs through additive Hom equivalences. It proves the elementary range and
kernel calculations needed to replace the transported differential by `1-T`.
Additivity follows from the additive equivalence, and naturality from naturality
of the triangle boundary and the shifted Hom coordinates.

New support module `CyclicDerivedFreeResolutionCoordinates` proves existence of a
normalized free-resolution datum for the original independent derived universes.
It extracts the already proved chain resolution, descends the differential and
canonical SES boundary through fully faithful localization, and identifies the
counit with the specified exact derived adjunction. No arbitrary object is chosen
from a holed existence statement: all its data is constructed in its proved
existence theorem and used only inside proofs.

New support module `CyclicDerivedFreeHomCoordinates` constructs the additive Hom
equivalences, proves the counit formula and naturality, and proves bijectivity of
the cyclic action from the derived equivalence and the structure isomorphisms.
The item imports the two calculation modules privately. Its existing public
import, all existing signatures, and all existing docstrings stay unchanged.

## Proved and sorry left

This is a decomposition, not a completed proof of the underlying cyclic calculus:
one original hole is closed syntactically and two strictly smaller calculation
holes are added. Direct hole change in delivered modules: +1.

Closed original hole:

- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonal_calculus`
  (`lem-sf-cyclic-derived-off-diagonal-calculus`). Its assembly proof is complete.

Added holes, and the only sorries in this delivery:

- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedFreeDefect_coordinates`
  (`lem-sf-cyclic-free-defect-coordinates`), in
  `Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates`.
  This only computes precomposition by the normalized differential; it asserts
  neither exactness nor a boundary property.
- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedFreeBoundary_comparison`
  (`lem-sf-cyclic-free-boundary-comparison`), in
  `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison`.
  This identifies the concrete free boundary with the unique presented boundary;
  it asserts neither additivity, naturality nor exactness.

The new existence theorem, Hom equivalences, counit formula, naturality formula,
action-bijectivity theorem, and private range/kernel arguments are fully proved.
The existing forgetting-zero theorem and boundary-hom definition remain intact.
All five delivered modules compile through lcompile.py; the final main-module
compile took 4.2 seconds. The supporting modules each compiled below 10 seconds.
Each remaining hole has its source, full argument in words, and its own DAG node.

The calculations were checked on the zero category and zero morphisms, on F=id
with identity endpoint actions (T=id and defect zero), and on the bilateral
free sequence at summand zero and summand -1. In the latter case the inverse
triangular action gives e d = j u, fixing the comparison sign. The identity
p(Tu)=T(u)-u also works in characteristic two and needs only bijectivity, not
any division or boundedness. All new statements retain unbounded complexes and
the original independent derived universes.

## No longer needed

None. No import or module is withdrawn. The original free-resolution and SES
triangle dependencies are used in the proved support bridge; the presentation
is used in the boundary comparison and the unchanged forgetting-zero theorem.
The Hom-out-of-triangle Mathlib leaf supplies the exactness argument. The DAG
now records these uses through the new support and calculation nodes.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing free-resolution theorem uses the
same universe for the two localizations, while this item's statement has
independent universes. The proved localization bridge resolves that mismatch
without changing a shared definition or statement.
The presentation uniqueness theorem states equality of presented values; its
proof text mentions the adjunct formula, but its signature does not expose that
formula. The new comparison statement isolates exactly the additional equality
needed here, rather than assuming that the formula follows from the signature.

## New nodes

`lem-sf-cyclic-free-resolution-coordinates` records the proved independent-universe
localization of the existing chain-level resolution, its normalized differential
and SES boundary, and its distinguished triangle. Module:
`Sheaf.CategoryTheory.CyclicDerivedFreeResolutionCoordinates`.

`lem-sf-cyclic-free-hom-coordinates` records the constructed additive Hom
coordinates, their counit and naturality formulas, and bijectivity of the cyclic
action. Module: `Sheaf.CategoryTheory.CyclicDerivedFreeHomCoordinates`.

`lem-sf-cyclic-free-defect-coordinates` records only the differential computation
in degrees zero and minus one. Module:
`Sheaf.CategoryTheory.CyclicDerivedFreeDefectCoordinates`.

`lem-sf-cyclic-free-boundary-comparison` records only the comparison of the
normalized free SES boundary with the uniquely presented off-diagonal boundary.
Module: `Sheaf.CategoryTheory.CyclicDerivedFreeBoundaryComparison`.

No change record is needed: no existing interface or definition was changed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
