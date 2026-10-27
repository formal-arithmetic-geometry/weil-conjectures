## What changed

Filled the proof of
`AlgebraicGeometry.AlgebraicSpace.representable_etale_fppf_local_lifting`
in `Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting`, preserving its signature
and imports. The proof follows the existing four-step DAG argument: use the étale
scheme-test pullback, transport surjectivity from the surjective scheme-test pullback
through their canonical Yoneda isomorphism, evaluate commutativity at the identity,
and show that the singleton fppf covering lies in the image sieve. Mathlib's
`Sheaf.epi_of_isLocallySurjective'` gives the epimorphism.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.AlgebraicSpace.representable_etale_fppf_local_lifting`
(node `lem-a1-representable-etale-fppf-local-lifting`).
One of one holes proved; zero holes added, zero split off, zero left in the module.
No additional project theorem with an unfinished proof is used by this proof.
Validation: the required remote `lcompile.py` compiled the module cleanly in 4.0 seconds.

## No longer needed

None. No imports removed, no dependency nodes or modules pruned. All four declared
proof dependencies are used: the scheme-test definitions, étaleness, fppf topology,
and the existing Mathlib sheaf-epimorphism leaf. No new proof imports are necessary.

## Where the brief, the DAG or earlier work was wrong

None. The separate étale and surjective scheme tests initially give different
representing schemes; the canonical isomorphism between their pullback squares
transports surjectivity to the chosen étale projection, as the existing docstring requires.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
