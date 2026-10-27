## What changed

Proved `AlgebraicGeometry.fppfSheafRepresentabilityDescentData` with its original signature.
The equivalence uses `fppfSchemeDataSheafGluing`, fully faithful sheaf restriction, and the
induced-category presentation of scheme descent data. Its local representations are the
ones furnished by the gluing theorem. Both directions of the geometric effectivity
criterion are proved using slice pullbacks, uniqueness of representing objects, and
compatibility of descent transitions with restriction.

All new helpers are private and proved. The categorical helpers are generic so checking
their identity-map computations does not unfold the concrete construction of schemes.
No public definitions, statements, attributes, or public imports were changed.
The node's proof and dependency lists now describe this route.
The static command check requested a record for the added universe names and elaboration
settings; `coord/changes/fppf-sheaf-descent-proof-elaboration.md` records these local
commands and all 299 current downstream modules. No consumer adaptation is needed.

Repair of return for head `516810ce197`: rebuilt the module from current shared source.
Preserved C7’s replacement proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` from commit `c7ce4ebd982`, then
reapplied the proved private helpers and theorem body. The returned packet had removed
the old affine-refinement import without incorporating that intervening replacement.
This packet explicitly retains the canonical source import; it is not an unchanged repush.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.fppfSheafRepresentabilityDescentData`
(node `lem-trf-fppf-sheaf-representability-descent-data`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
No statements were split off, and no definitions contain postponed proofs.

Original validation: the complete module compiled in 29.6 seconds without warnings.
Repair validation: the module with C7’s canonical import compiles against the current
published build in 38.2 seconds, with no errors or warnings and zero local holes.
`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound`, and an inherited
`sorryAx` through imported proof dependencies. This delivery closes the assigned local
hole from the existing library declarations; it does not claim to close their transitive
proof obligations. The original signature and public imports were compared verbatim.

## No longer needed

The previous packet removed the old direct proof import
`Sheaf.AlgebraicGeometry.FppfAffineRefinement`. Current main has already replaced it with
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`; this repair preserves that import.
The proof uses Mathlib’s subcanonical fppf topology and subcanonical slice topologies.
Replaced the broad module
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` with the directly used
`Mathlib.CategoryTheory.Comma.Over.Pullback`. Also removed redundant direct imports
`Sheaf.CategoryTheory.SiteCoveringAxioms` and
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`, both publicly available through
`SchemeCoverDescentDatum`.

The revised node no longer directly needs `def-weil-pbc-fpqc-covering`,
`def-weil-pbc-sites-and-cohomology`, `lem-pc-fppf-affine-refinement`,
`lem-weil-pbc-fpqc-representable-descent`,
`lem-trf-fppf-local-representations-fully-faithful`, or `def-pd-descent-datum`.
The latter definition remains a statement dependency, and the general sites definition
remains a statement dependency as well. Removed the obsolete affine-refinement entry
from the node's top-level `tool_uses`.

In particular the separate forward-functor module
`Sheaf.AlgebraicGeometry.FppfLocalRepresentationsFullyFaithful` is unnecessary for this
proof: local slice representations immediately package a preimage of every locally
representable sheaf, while sheaf descent supplies full faithfulness. These are removals
from this proof's direct dependencies; no other module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned statement is unchanged and needs no repair. The original route repeated
Mathlib's subcanonicity result and built a separate forward functor. Both can be omitted
with the existing definition of scheme descent data as represented local sheaves.
The effectivity clause still requires a genuine argument: its identity-test invariance
extends to arbitrary overlap-slice objects by pullback compatibility of transitions.
That extension and both directions of effectivity are proved in this delivery.

The original declaration docstring retains its historical nine-step plan; the node's
updated four-step proof records the actual shorter implementation.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
