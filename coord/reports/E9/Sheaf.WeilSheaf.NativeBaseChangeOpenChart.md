## What changed

Proved `AlgebraicGeometry.ProEtale.adicDerivedBaseChange_openChart` in
`Sheaf.WeilSheaf.NativeBaseChangeOpenChart`, preserving both public declarations,
their signatures, and all public imports.

The proof constructs the map from the canonical iterated pullback to X' and proves
its square over j Cartesian by pullback pasting and cancellation. It identifies
the specified exchange along either open restriction with the existing native
open base-change isomorphism: iterated mates and the native compositor conjugate
equations give the ordinary equality, and `derived_exact_forget_mate` derives it.
Private, fully proved helpers normalize triple inverse images and establish the
six-face pullback cube using the existing native compositor associativity law.
`mapDerivedCategory_exactCube` lifts this equality to derived categories.
`exchangeMate_cube` then supplies exactly the commutativity equation for
`Arrow.isoMk`, with the two open exchange isomorphisms as its vertical comparisons.

Added only private proof imports of native adic base change, native compositor
coherence, `DerivedForgetMate`, `DerivedExactCube`, and `ExchangeMateCube`. Updated
the item's DAG proof and dependencies to describe this argument. No shared
interface, definition, consumer, target, or other existing module changed.
Native functors are marked irreducible only locally in this proof file; the private
normalization definitions return isomorphisms at a specified sheaf to keep type
checking small.

Validation: the final item compiles cleanly in 13.8 seconds through `lcompile.py`.
The unchanged direct consumer `Sheaf.WeilSheaf.GeometricProperBaseChange` also
compiles against it (temporary consumer copy removed from the packet).
`#print axioms AlgebraicGeometry.ProEtale.adicDerivedBaseChange_openChart` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.adicDerivedBaseChange_openChart`.
`AlgebraicGeometry.ProEtale.adicChartSquare` retains its existing complete proof.
The item's module has zero `sorry`; zero holes were added or split off. All new
private helper proofs are complete, including the native pullback cube and the
ordinary/derived open-mate identifications.

## No longer needed

None. Every original declared proof dependency is used. No original import was
removed and no node or module was withdrawn. No additional geometric reduction,
properness, boundedness, constructibility, or coefficient comparison is needed.

## Where the brief, the DAG or earlier work was wrong

The original statement and proof plan are correct. The plan's localization and
unit/counit compatibility steps can be implemented using the already proved
`derived_exact_forget_mate` and `mapDerivedCategory_exactCube`, rather than adding
another split obligation. The DAG now names these two generic dependencies.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
