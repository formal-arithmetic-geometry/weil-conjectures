## What changed

Proved `WeilConjectures.sfSupportTransition_presentation` with its original signature,
its original public import, and the original construction `sfSupportPresentationLevel`.
All added helpers are private and proved. No other existing Lean module changes.

The proof explicitly identifies both ordinary and derived scalar-restriction composition
maps. Transposition under the published higher scalar adjunction identifies the two
reduction arrows. Exact-localization coherence transports the supplied ordinary open
square to derived categories, and naturality gives the adjacent open square before
direct image. The direct-image comparison is identified using its section normalization
and uniqueness of the K-injective normalization. The ordinary section comparison is
proved over arbitrary finite coefficient rings and then specialized as a functor equality,
avoiding reduction of the concrete quotient-ring presentations. The uniqueness argument resolves the
restricted complex and cancels a tail proved invertible from the normalization equation;
it does not require restriction to preserve K-injective complexes. Finally,
`restrictedComparison` uses naturality of direct image and the completed restriction
composition map to produce the stated equality of specified transitions.

The node's proof steps now describe these actual Lean arguments. There are no new data
constructions, selected witnesses, public instances, mathematical assumptions, or changes
to shared definitions.

Validation: the complete module compiled on the project server in 37.5 seconds,
within the 60-second limit. Profiling options and the temporary section-calculation
probe were removed before delivery. Both original public signatures and the entire
original `sfSupportPresentationLevel` construction were checked textually unchanged.
All Lean source lines are at most 100 characters.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.sfSupportTransition_presentation`
(node `lem-sf-support-adjacent-presentation`).

The item has zero remaining sorries. Zero holes are added elsewhere, and no statements
are split off. This is one hole closed, rather than a decomposition. The existing
`sfSupportPresentationLevel` definition remains the same mapIso construction.

## No longer needed

No import is removed. No module or DAG node is pruned; the original dependencies still
supply the definitions and normalized comparison interfaces used by this proof.
The proof does not invoke the existence theorem `sfFiniteOpenPresentation`: the original
signature already supplies its ordinary comparisons and their compatibility. It also
does not invoke the existence theorem `compactSupportProperImageTower`, since the
normalized operation data are supplied in the signature. Their modules remain needed
for the predicates, definitions and normalization fields, so neither is declared unused.

No additional exactness module or unproved comparison lemma is imported. Exactness of
the intrinsic open functor is transported from the supplied slice comparison locally.
The source library under `WeilConjectures` is untouched.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned normalization and presentation identifications
were genuine glue obligations, but the existing interfaces suffice: they require no new
split statement. The equality of the restriction-composition maps needs an explicit
uniqueness and localization-coherence argument; equality of their underlying section
formulas alone is not substituted for equality of the specified derived arrows.

The argument uses arbitrary schemes and arbitrary unbounded completed-coefficient K.
The first index n=0 still uses positive coefficient exponents 1 and 2. Empty and identity
opens and the zero complex require no exceptional case, since the proof uses only the
supplied natural isomorphisms, adjunction equations, localization and functoriality.
The blueprint unit's realized statements and steps are unchanged.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
