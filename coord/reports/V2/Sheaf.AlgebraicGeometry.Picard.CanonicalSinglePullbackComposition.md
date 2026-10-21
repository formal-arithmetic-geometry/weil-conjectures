## What changed

Restored and repaired the complete proof of
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition` from the
previous reviewed delivery. The proof uses the already proved upstream
`perfectHomTensorCounit_comp` for the selected factorization at the single
complex, applies counit naturality, and uses the proved upstream
`homotopySinglePullbackComposition` compatibility. Proved private generic
helpers handle associativity and functoriality; a private equation unfolds
`canonicalSinglePullbackMap` once. This avoids repeatedly reducing the large
chosen-adjunction and derived-counit expressions. The theorem statement and its
mathematical meaning are unchanged. Local irreducibility annotations protect
`tensorPullback` and `Adjunction.leftAdjointUniq` during this proof; they change
no library definition or exported attribute.

The proof imports the adopted upstream helper
`WeilConjectures.AlgebraicGeometry.Picard.HomotopySinglePullbackComposition`
and `WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit`, both privately.
The complete restored module compiles cleanly under the 60-second limit
(53.0 seconds in the final single-file check).
No public declaration, definition, or axiom was added. The existing DAG node
now records the use of `lem-pc-perfect-hom-cochain-counit`.

## Proved and sorry left

This is a zero-hole rework assignment: the quarantined module already had a
complete proof, but did not elaborate after the upstream sync. Repaired
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition`;
0 original holes closed, 0 holes added or split off.
No `sorry` remains in the delivered module and no holes were added. The imported
upstream helper and the selected derived composition witness retain whatever
proof status they have in the shared library.

## No longer needed

No mathematical dependency was pruned. Direct evaluation of the derived lift
is replaced by the existing `perfectHomTensorCounit_comp`;
`lem-pc-ringed-spaces-derived-pullback-composition` remains needed transitively
through `lem-pc-perfect-hom-cochain-counit`. The helper
`lem-pc-homotopy-single-pullback-composition` is consumed from its adopted
`WeilConjectures` module. The item's public comparison import remains necessary
for `canonicalSinglePullbackMap`; the derived composition declaration and the
adjunction declarations remain transitive proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The prior reviewed delivery was reverted during a cluster restore, leaving this
module quarantined. During the intervening upstream sync,
`AlgebraicGeometry.Scheme.Modules.derivedPullback` became a distinct local name
that shadows the intended `AlgebraicGeometry.derivedPullback` inside this
namespace. The restored proof qualifies the latter at the affected occurrences;
this is a forced compatibility edit and leaves the elaborated theorem signature
and target statement unchanged. No mathematical error in the DAG statement or
proof route was found.

The required compatibility record is
`coord/changes/V2-canonical-single-pullback-composition-restoration.md`. It
records the unchanged intended signature, local elaboration annotations, and
the three quarantined direct consumers. No consumer adaptation is forced.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
