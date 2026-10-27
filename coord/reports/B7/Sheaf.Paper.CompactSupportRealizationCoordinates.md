## What changed

Proved `WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrict_kInjective`
in the assigned module. The proof compares the two actual section-localization
presentations, identifies their map with `A.inclusion` using its normalization,
and applies the existing exact-localization and ordinary-adjunction theorems.
Restrictions along the coefficient isomorphisms and the encoding equivalence
preserve K-injective complexes, and the existing restriction-composition
isomorphisms assemble the required composite.

Added only private, proved helpers and private proof imports. Existing public
signatures, definitions, imports, instances and target statements are unchanged.
The setup node now records the proof and its actual dependencies.
The full file compiled through lcompile in 47.1 seconds; two redundant simp
arguments were then removed for the final delivery compile.

Searches: LeanFinder returned generic flat scalar-extension results; Loogle did
not know the project's K-injective class; remote Mathlib grep found no specialized
normalization theorem. Local searches found the exact scalar-localization theorem,
the normalized ordinary scalar adjunction, and the continuous-coefficient
localization comparison, which the proof reuses.

## Proved and sorry left

Closed 1 of the 2 original holes:
`WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrict_kInjective`.
No holes added and no statements split off.

The one remaining hole is unchanged:
`WeilConjectures.CompactSupportFactorNormalization.ordinaryRestrictionSquare_existsUnique`
(node `lem-zl-compact-support-realization-coordinates-setup`). Its original
identity-on-sections statement and proof plan are retained.

## No longer needed

None. No original import, module or dependency node is withdrawn. The remaining
square obligation still needs its coefficient-normalization dependencies. All new
proof imports are used.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The uniformizer-localization step requires an explicit
comparison between ringed-section localization and the existing continuous-function
localization presentation; the delivery supplies it by identity on fraction rings
and naturality of sheafification, without adding geometric assumptions.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
