## What changed

Proved `AlgebraicGeometry.Etale.etaleProperAmbientTransport_comp` by comparing hom
components. The proof obtains Cartesian vertical exchange pasting directly from
`etaleProperOpenExchangeCube`, derives the forward and inverse versions of
composition coherence with prescribed scheme-map equalities from the existing
`push_derived_assoc` helper, and combines these identities using naturality.

Added proof imports of `Sheaf.AlgebraicGeometry.EtaleProperOpenExchangeCube` and
`all Sheaf.Paper.DerivedCompactSupportCompositionCoherence`. The latter exposes the
already proved private associativity helper; its other structural-loop theorem is
not needed. All new helpers in the item are private and proved. Updated the node's
proof, proof dependencies, and proof origin to describe this implementation.
The original theorem signature, definitions, and public import are preserved.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.etaleProperAmbientTransport_comp`
(`lem-pur-etale-proper-ambient-transport-composition`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean module: 0.
No statements were split off. The complete module compiled cleanly through
`lcompile.py` in 10.2 seconds, with exit code 0 and no warnings.

## No longer needed

No imports were removed and no modules were withdrawn. The immediate proof no
longer invokes `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`:
its generic composition-existence theorem is replaced in `proof_deps` by
`lem-amb-derived-compact-support-composition-coherence`, whose module already
proves the concrete associativity identity for the specified compositors.
The ringed-topos composition module remains transitively imported by existing
interfaces; this delivery does not claim to prune it from the targets' closure.
No graph, compactification, neighborhood-intersection, or graph-comparison lemma
is used in this proof beyond the existing transport definition.

## Where the brief, the DAG or earlier work was wrong

The planned categorical argument is valid. The generic ringed-topos composition
statement listed in the original proof dependencies does not itself expose the
needed associativity law for `rightDerivedLowerStarCompOfEq`. The proved concrete
mate-associativity helper supplies that API, so no new mathematical obligation is
necessary. Properness of the neighborhood maps is obtained from the Cartesian
squares; properness of the initial or terminal maps is never assumed. No unit
statement or unit proof step is bypassed, and there is no definition or statement
repair.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
